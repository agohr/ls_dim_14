import QuaternionicSymmetry.QuaternionicManifoldKernelOperatorProperties

/-! Differentiability in a manifold chart of the actual local scalar and
symplectic factors. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProductGaugeDifferential

open scoped Manifold ContDiff Quaternion
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldSmoothProductLifts
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem differentiableAt_chartPullback {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M → F) (s : Set M) (hs : IsOpen s)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f s)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈ s) :
    DifferentiableAt ℝ (fun z => f ((extChartAt 𝓘(ℝ, E) p).symm z)) y := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hfAt : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x :=
    (hf x hx).contMDiffAt (hs.mem_nhds hx)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (extChartAt 𝓘(ℝ, E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  exact (hfAt.comp y hsymm).contDiffAt.differentiableAt (by norm_num)

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem scalarLift_chart_differentiableAt (p : M) (i j : atlas E M)
    (q : unitary ℍ) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈ liftNeighborhood Q i j q) :
    DifferentiableAt ℝ
      (fun z => scalarLiftRaw Q i j q ((extChartAt 𝓘(ℝ, E) p).symm z)) y := by
  exact differentiableAt_chartPullback (scalarLiftRaw Q i j q)
    (liftNeighborhood Q i j q) (isOpen_liftNeighborhood Q i j q)
    (smooth_scalarLiftRaw Q i j q) p y hy hx

theorem symplecticFactor_chart_differentiableAt (p : M) (i j : atlas E M)
    (q : unitary ℍ) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈ liftNeighborhood Q i j q) :
    DifferentiableAt ℝ
      (fun z => symplecticFactorOperator S Q i j q
        ((extChartAt 𝓘(ℝ, E) p).symm z)) y := by
  exact differentiableAt_chartPullback (symplecticFactorOperator S Q i j q)
    (liftNeighborhood Q i j q) (isOpen_liftNeighborhood Q i j q)
    (smooth_symplecticFactorOperator S Q i j q) p y hy hx

end
end QuaternionicSymmetry.QuaternionicManifoldProductGaugeDifferential
