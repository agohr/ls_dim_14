import QuaternionicSymmetry.QuaternionicManifoldWeylMatrixExpansion
import QuaternionicSymmetry.QuaternionicWeylExteriorTrace
import QuaternionicSymmetry.QuaternionicCorrectedSourceTraceForms

/-! Actual normalized standard trace forms are the canonical pairings of
the exterior signed traces used in the orbital positivity argument. -/
namespace QuaternionicSymmetry.QuaternionicManifoldWeylTraceForms
open Module ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicManifoldWeylMatrixExpansion QuaternionicWeylExteriorTrace
open QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureMatrixExpansion
open QuaternionicCorrectedSourceTraceForms ComplexExteriorTraceBridge
open QuaternionicManifoldFixedSolder ContinuousAlgebraWedgePowers
open ExteriorContinuousPairing LocalChernWeilTracePowers ManifoldDifferentialForms
open QuaternionicProjectiveStandardHilbertStructure
open scoped Manifold ContDiff Matrix
noncomputable section
variable {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedRing (Matrix
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension)
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension)
    (Fin (standardStructure S).quaternionicDimension ⊕ Fin (standardStructure S).quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedAlgebra

theorem sourceMatrixForm_eq_weyl
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (b : Basis ι ℝ E) (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy) :
    ∃ (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
      (hW : HyperWeylFiber S W),
      (sourceMatrixForm S Q D t p y hy).compContinuousLinearMap
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap =
      combinationForm (fun a : Index S => (sourceMatrixMap S (operatorBasis S a)).val)
        (coefficientTwo S W (HyperWeylFiber.mem_skewCentralizer S hW) b) := by
  obtain ⟨W, hW, _, hexp⟩ := correctedCurvature_finite_expansion S Q D hsp hdecomp b t p y hy ht
  refine ⟨W, hW, ?_⟩
  apply ContinuousAlternatingMap.ext
  intro v
  change sourceMatrixForm S Q D t p y hy
    (fun i => (fixedSolderEquiv S Q p y hy).symm (v i)) = _
  rw [sourceMatrixForm_apply, hexp]
  simp only [← fixedSolderEquiv_apply S Q p y hy,
    ContinuousLinearEquiv.apply_symm_apply, combinationForm,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro a _
  congr 1

theorem closedSourceTrace_eq_weyl
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (b : Basis ι ℝ E) (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy) :
    ∃ (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
      (hW : HyperWeylFiber S W),
      ∀ (j : ℕ) (_hj : 0 < j) (v : Fin (powerDegree (2 * j - 1)) → E),
        inChartModel p (closedSourceEvenTrace S Q D t j).val.val y
          (fun i => (fixedSolderEquiv S Q p y hy).symm (v i)) =
        toContinuous (powerDegree (2 * j - 1))
          (traceRepresentative S W (HyperWeylFiber.mem_skewCentralizer S hW) b j) v := by
  obtain ⟨W, hW, hform⟩ := sourceMatrixForm_eq_weyl S Q D hsp hdecomp b t p y hy ht
  refine ⟨W, hW, ?_⟩
  intro j hj v
  rw [closedSourceEvenTrace_chart S Q D t j hj p y hy]
  have hp := power_comp (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap
    (sourceMatrixForm S Q D t p y hy) (2 * j - 1)
  rw [hform] at hp
  have hv := congrArg (fun α => α v) hp
  change power (sourceMatrixForm S Q D t p y hy) (2 * j - 1)
    (fun i => (fixedSolderEquiv S Q p y hy).symm (v i)) = _ at hv
  rw [hv]
  exact (paired_signedTrace _ _ j v).symm

end
end QuaternionicSymmetry.QuaternionicManifoldWeylTraceForms
