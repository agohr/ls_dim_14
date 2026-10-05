import QuaternionicSymmetry.QuaternionicManifoldLocalScalarLifts

/-! Operator-coordinate smoothness of both factors in the actual local
`Sp(n)·Sp(1)` lift of adapted tangent transitions. -/

namespace QuaternionicSymmetry.QuaternionicManifoldSmoothProductLifts

open VectorBundleFrameTransitions
  QuaternionicManifoldFixedNormalizer
  QuaternionicManifoldLocalScalarLifts
open scoped ContDiff Manifold Quaternion

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

def scalarActionLinear : ℍ →ₗ[ℝ] (E →L[ℝ] E) where
  toFun q := Module.End.toContinuousLinearMap E (S.action q)
  map_add' q r := by
    ext v
    simp
  map_smul' a q := by
    ext v
    simp

omit [Nontrivial E] in
theorem scalarActionLinear_apply (q : ℍ) (v : E) :
    scalarActionLinear S q v = S.action q v := rfl

def fixedTransitionCLM (i j : atlas E M) (x : M) : E →L[ℝ] E :=
  ((modelGauge S (Q.reduction.Q j)).symm.toContinuousLinearMap).comp
    ((Q.frames.coordChange i j x).comp
      (modelGauge S (Q.reduction.Q i)).toContinuousLinearMap)

omit [Nontrivial E] in
theorem smooth_fixedTransitionCLM (i j : atlas E M) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fixedTransitionCLM S Q i j) (overlap Q i j) := by
  have hcoord := Q.frames.smooth_coordChange i j
  have hright : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun x : M => (Q.frames.coordChange i j x).comp
        (modelGauge S (Q.reduction.Q i)).toContinuousLinearMap)
      (overlap Q i j) :=
    hcoord.clm_comp contMDiffOn_const
  exact contMDiffOn_const.clm_comp hright

def scalarInverseOperator (i j : atlas E M) (q : unitary ℍ) (x : M) :
    E →L[ℝ] E :=
  scalarActionLinear S (star (scalarLiftRaw Q i j q x))

private def starLinear : ℍ →ₗ[ℝ] ℍ where
  toFun := star
  map_add' a b := by simp
  map_smul' r a := by simp [Quaternion.star_smul]

theorem smooth_scalarInverseOperator (i j : atlas E M) (q : unitary ℍ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (scalarInverseOperator S Q i j q) (liftNeighborhood Q i j q) := by
  have hstar : ContDiff ℝ ∞ (star : ℍ → ℍ) :=
    starLinear.toContinuousLinearMap.contDiff
  have hraw := smooth_scalarLiftRaw Q i j q
  have hstarRaw : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℍ) ∞
      (fun x : M => star (scalarLiftRaw Q i j q x))
      (liftNeighborhood Q i j q) :=
    (hstar.contMDiff).comp_contMDiffOn hraw
  exact (scalarActionLinear S).toContinuousLinearMap.contMDiff.comp_contMDiffOn hstarRaw

def symplecticFactorOperator (i j : atlas E M) (q : unitary ℍ) (x : M) :
    E →L[ℝ] E :=
  (scalarInverseOperator S Q i j q x).comp (fixedTransitionCLM S Q i j x)

theorem smooth_symplecticFactorOperator (i j : atlas E M) (q : unitary ℍ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (symplecticFactorOperator S Q i j q)
      (liftNeighborhood Q i j q) := by
  exact (smooth_scalarInverseOperator S Q i j q).clm_comp
    ((smooth_fixedTransitionCLM S Q i j).mono Set.inter_subset_left)

omit [Nontrivial E] in
theorem fixedTransitionCLM_eq (i j : atlas E M) (y : M)
    (hi : y ∈ Q.frames.adaptedCore.baseSet i)
    (hj : y ∈ Q.frames.adaptedCore.baseSet j) :
    fixedTransitionCLM S Q i j y =
      (fixedTransition S Q i j y hi hj).toContinuousLinearMap := by
  ext v
  change (modelGauge S (Q.reduction.Q j)).symm
      (Q.frames.coordChange i j y
        (modelGauge S (Q.reduction.Q i) v)) =
    (modelGauge S (Q.reduction.Q j)).symm
      (ManifoldQuaternionicUnitaryNormalizer.frameTransitionIsometry
        Q i j y hi hj (modelGauge S (Q.reduction.Q i) v))
  rw [ManifoldQuaternionicUnitaryNormalizer.frameTransitionIsometry_apply]

theorem scalarInverseOperator_eq (i j : atlas E M)
    (q : unitary ℍ) (y : M)
    (hy : y ∈ liftNeighborhood Q i j q) :
    scalarInverseOperator S Q i j q y =
      (QuaternionicUnitScalarIsometries.unitQuaternionNormalizerAction S
        (scalarLiftUnit Q S i j q y hy)).1.symm.toContinuousLinearMap := by
  ext v
  rfl

/-- The smooth operator formula is exactly the quaternion-linear factor in
the pointwise product decomposition, expressed in operator coordinates. -/
theorem exists_smooth_operator_factor (i j : atlas E M)
    (q : unitary ℍ) (y : M)
    (hy : y ∈ liftNeighborhood Q i j q) :
    ∃ h : QuaternionicIsometryNormalizer.symplecticKernel S,
      h.1.1.toContinuousLinearMap = symplecticFactorOperator S Q i j q y ∧
      QuaternionicUnitScalarIsometries.symplecticProductAction S
        (h, scalarLiftUnit Q S i j q y hy) =
          QuaternionicManifoldPointwiseLifts.fixedTransitionNormalizer
            S Q i j y hy.1.1 hy.1.2 := by
  obtain ⟨h, hh⟩ := local_product_factor Q S i j q y hy
  refine ⟨h, ?_, hh⟩
  let T := QuaternionicUnitScalarIsometries.unitQuaternionNormalizerAction S
    (scalarLiftUnit Q S i j q y hy)
  have hprod : h.1 * T =
      QuaternionicManifoldPointwiseLifts.fixedTransitionNormalizer
        S Q i j y hy.1.1 hy.1.2 := hh
  have heq : h.1 = T⁻¹ *
      QuaternionicManifoldPointwiseLifts.fixedTransitionNormalizer
        S Q i j y hy.1.1 hy.1.2 := by
    rw [← hprod]
    have hcomm := QuaternionicUnitScalarIsometries.symplecticKernel_commutes_unitQuaternion
      S h (scalarLiftUnit Q S i j q y hy)
    change h.1 * T = T * h.1 at hcomm
    rw [hcomm]
    group
  ext v
  rw [heq]
  change (T.1.symm)
      ((fixedTransition S Q i j y hy.1.1 hy.1.2) v) =
    (scalarInverseOperator S Q i j q y)
      (fixedTransitionCLM S Q i j y v)
  rw [scalarInverseOperator_eq S Q i j q y hy,
    fixedTransitionCLM_eq S Q i j y hy.1.1 hy.1.2]
  rfl

end
end QuaternionicSymmetry.QuaternionicManifoldSmoothProductLifts
