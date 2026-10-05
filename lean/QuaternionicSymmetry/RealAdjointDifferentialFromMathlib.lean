import QuaternionicSymmetry.LieGroupIdentityChart

/-! The derivative of the actual adjoint action is the actual Lie bracket.
The calculation uses the multiplication matrices in the identity chart,
with the two mixed derivatives identified by Schwarz symmetry. -/
namespace QuaternionicSymmetry.RealAdjointDifferentialFromMathlib

open LocalAdjointDifferential LieGroupIdentityChart GeneralRealAdjointDifferentialSource
open VectorField
open scoped Manifold ContDiff Topology
open Filter Function Set
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]

local notation "e₁" => identityChart (E := E) (G := G)
local notation "a₁" => identityCoordinate (E := E) (G := G)
local notation "A₁" => leftMatrix (chartMul (E := E) (G := G)) a₁

lemma inverse_chart_symm_derivative {x : E} (hx : x ∈ (e₁).target) :
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (e₁).symm x).inverse =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e₁ ((e₁).symm x) := by
  apply ContinuousLinearMap.inverse_eq
  · simpa using mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
      (I := 𝓘(ℝ,E)) (x := (1 : G)) hx
  · simpa using mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
      (I := 𝓘(ℝ,E)) (x := (1 : G)) hx

lemma invariantField_in_coordinates (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    mpullback 𝓘(ℝ,E) 𝓘(ℝ,E) (e₁).symm (mulInvariantVectorField v) =ᶠ[𝓝 a₁]
      (fun x => A₁ x v) := by
  filter_upwards [eventually_regular_chart (E := E) (G := G)] with x hx
  rw [leftMatrix_eq_mfderiv hx.1 hx.2.1]
  unfold mpullback
  rw [inverse_chart_symm_derivative hx.1]
  rfl

lemma bracket_in_coordinates (u v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    ⁅u,v⁆ = (fderiv ℝ A₁ a₁ u) v - (fderiv ℝ A₁ a₁ v) u := by
  have hu := invariantField_in_coordinates u
  have hv := invariantField_in_coordinates v
  have hA : DifferentiableAt ℝ A₁ a₁ :=
    (leftMatrix_contDiffAt ((contDiffAt_infty.mp chartMul_smooth) 2)).differentiableAt
      (by norm_num)
  have h₁ := (hA.hasFDerivAt.clm_apply (hasFDerivAt_const v a₁)).fderiv
  have h₂ := (hA.hasFDerivAt.clm_apply (hasFDerivAt_const u a₁)).fderiv
  rw [GroupLieAlgebra.bracket_def, mlieBracket, mlieBracketWithin_apply,
    chart_center_derivative]
  simp only [ModelWithCorners.range_eq_univ, Set.preimage_univ, Set.univ_inter,
    mpullbackWithin_univ, lieBracketWithin_univ]
  have hid : (ContinuousLinearMap.id ℝ E).inverse = ContinuousLinearMap.id ℝ E := by
    exact ContinuousLinearMap.inverse_eq (by ext; rfl) (by ext; rfl)
  rw [hid]
  change lieBracket ℝ
    (mpullback 𝓘(ℝ,E) 𝓘(ℝ,E) (e₁).symm (mulInvariantVectorField u))
    (mpullback 𝓘(ℝ,E) 𝓘(ℝ,E) (e₁).symm (mulInvariantVectorField v)) a₁ = _
  simp only [lieBracket_eq]
  rw [hu.fderiv_eq, hv.fderiv_eq, hu.self_of_nhds, hv.self_of_nhds]
  dsimp only
  rw [leftMatrix_center, h₁, h₂]
  simp

lemma adjoint_coordinate_differential (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    DifferentiableAt ℝ (fun x => adjointOrbitReal v ((e₁).symm x)) a₁ ∧
      ∀ u : GroupLieAlgebra 𝓘(ℝ,E) G,
        fderiv ℝ (fun x => adjointOrbitReal v ((e₁).symm x)) a₁ u = ⁅u,v⁆ := by
  have hcalc := quotient_differential ((contDiffAt_infty.mp
    (chartMul_smooth (E := E) (G := G))) 2) leftMatrix_center rightMatrix_center
    rightMatrix_eventually_invertible v
  have heq := adjoint_eq_matrix_quotient v
  refine ⟨hcalc.1.congr_of_eventuallyEq heq, fun u => ?_⟩
  rw [heq.fderiv_eq, hcalc.2 u, bracket_in_coordinates]

lemma adjoint_differential (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (adjointOrbitReal v) 1 ∧
      ∀ u : GroupLieAlgebra 𝓘(ℝ,E) G,
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (adjointOrbitReal v) 1 u = ⁅u,v⁆ := by
  have hcalc := adjoint_coordinate_differential v
  have hd : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (adjointOrbitReal v) 1 := by
    apply (mdifferentiableAt_iff_source_of_mem_source (I := 𝓘(ℝ,E))
      (mem_chart_source E (1 : G))).mpr
    simpa using hcalc.1.mdifferentiableAt.mdifferentiableWithinAt
  have hx : HasFDerivAt (fun x => adjointOrbitReal v ((e₁).symm x))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (adjointOrbitReal v) 1) a₁ := by
    simpa [writtenInExtChartAt] using hd.hasMFDerivAt.2
  refine ⟨hd, fun u => ?_⟩
  rw [← hx.fderiv]
  exact hcalc.2 u

/-- The exact BG-L9 contract, now a theorem of the Lean development. -/
theorem realAdjointDifferential : LeeRealAdjointDifferentialSource := by
  intro E G _ _ _ _ _ _ _ _ _ _ v
  exact adjoint_differential v

end
end QuaternionicSymmetry.RealAdjointDifferentialFromMathlib
