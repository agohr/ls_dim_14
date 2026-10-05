import QuaternionicSymmetry.FourDimensionalHalfSpinActualCliffordTransition
import QuaternionicSymmetry.QuaternionicManifoldSmoothProductLifts

/-! Actual adapted transitions have locally smooth raw quaternion factors.  The
right factor is recovered by evaluating the already smooth quaternion-linear
kernel operator at `1`; its unit property and the two-sided/Clifford identities
hold on the genuine refined overlap, without a global spin lift. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinSmoothLocalFactors

open scoped ContDiff Manifold Quaternion
open QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldSmoothProductLifts
  QuaternionicManifoldPointwiseLifts
  QuaternionicIsometryNormalizer
  QuaternionicUnitScalarIsometries
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicLeftLineAction
  FourDimensionalHalfSpinTwoSidedOrthogonal
  FourDimensionalHalfSpinNormalizerTwoSided
  FourDimensionalHalfSpinNormalizerAction
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinCliffordActual
  FourDimensionalHalfSpinCliffordCovariance

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def localRightRaw (i j : atlas ℍ M) (q₀ : unitary ℍ) (y : M) : ℍ :=
  star (symplecticFactorOperator leftLineStructure Q i j q₀ y 1)

theorem smooth_localRightRaw (i j : atlas ℍ M) (q₀ : unitary ℍ) :
    ContMDiffOn 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) ∞
      (localRightRaw Q i j q₀) (liftNeighborhood Q i j q₀) := by
  have hoperator := smooth_symplecticFactorOperator leftLineStructure Q i j q₀
  have hvalue : ContMDiffOn 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) ∞
      (fun y : M => symplecticFactorOperator leftLineStructure Q i j q₀ y 1)
      (liftNeighborhood Q i j q₀) :=
    hoperator.clm_apply contMDiffOn_const
  have hstar : ContDiff ℝ ∞ (star : ℍ → ℍ) := by
    let f : ℍ →ₗ[ℝ] ℍ :=
      { toFun := star
        map_add' a b := by simp
        map_smul' r a := by simp [Quaternion.star_smul] }
    exact f.toContinuousLinearMap.contDiff
  exact hstar.contMDiff.comp_contMDiffOn hvalue

/-- The smooth raw values are genuine unit factors of the actual transition;
the same factors intertwine literal Clifford multiplication. -/
theorem local_factors_clifford (i j : atlas ℍ M) (q₀ : unitary ℍ)
    (y : M) (hy : y ∈ liftNeighborhood Q i j q₀) :
    ∃ q r : unitary ℍ,
      (q : ℍ) = scalarLiftRaw Q i j q₀ y ∧
      (r : ℍ) = localRightRaw Q i j q₀ y ∧
      (fixedTransitionNormalizer leftLineStructure Q i j y hy.1.1 hy.1.2).1 =
        twoSidedIsometry q r ∧
      (∀ p : ProjectiveSpinor,
        spinorTransition Q i j y hy.1.1 hy.1.2 p =
          projectiveHalfSpin q p) ∧
      (∀ u : ℍ, ∀ v : Spinor,
        cliffordMultiply
          ((fixedTransitionNormalizer leftLineStructure Q i j y hy.1.1 hy.1.2).1 u)
          (halfSpinLinearEquiv q v) =
            halfSpinLinearEquiv r (cliffordMultiply u v)) := by
  let q := scalarLiftUnit Q leftLineStructure i j q₀ y hy
  obtain ⟨h, hoperator, hprod⟩ :=
    exists_smooth_operator_factor leftLineStructure Q i j q₀ y hy
  obtain ⟨r, hr⟩ := kernel_eq_right h
  have hraw : (r : ℍ) = localRightRaw Q i j q₀ y := by
    unfold localRightRaw
    rw [← hoperator, hr]
    simp [rightUnitIsometry_apply]
  have hreal :
      (fixedTransitionNormalizer leftLineStructure Q i j y hy.1.1 hy.1.2).1 =
        twoSidedIsometry q r := by
    have hprod' := congrArg Subtype.val hprod
    change h.1.1 * (unitQuaternionNormalizerAction leftLineStructure q).1 =
      (fixedTransitionNormalizer leftLineStructure Q i j y hy.1.1 hy.1.2).1
      at hprod'
    rw [← hprod', hr]
    apply LinearIsometryEquiv.ext
    intro u
    simp [twoSidedIsometry_apply, rightUnitIsometry_apply,
      unitQuaternionNormalizerAction, unitQuaternionAction,
      unitScalarIsometry_apply, action_eq_mul, mul_assoc]
  refine ⟨q, r, rfl, hraw, hreal, ?_, ?_⟩
  · intro p
    let g := fixedTransitionNormalizer leftLineStructure Q i j y hy.1.1 hy.1.2
    let k := productLift leftLineStructure g
    have hk : symplecticProductAction leftLineStructure k =
        symplecticProductAction leftLineStructure (h, q) := by
      rw [productLift_spec, hprod]
    exact projective_factor_independent leftLineStructure k (h, q) hk p
  · intro u v
    rw [hreal, twoSidedIsometry_apply]
    exact cliffordMultiply_twoSided q r u v

/-- Every actual adapted-frame overlap point has a genuine open refinement
with smooth raw factors for both chiral representations. Their pointwise
unit lifts simultaneously realize the real tangent transition, projective
half-spin transition, and Clifford covariance. -/
theorem exists_local_smooth_clifford_factors (i j : atlas ℍ M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) :
    ∃ q₀ : unitary ℍ,
      x ∈ liftNeighborhood Q i j q₀ ∧
      IsOpen (liftNeighborhood Q i j q₀) ∧
      ContMDiffOn 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) ∞
        (scalarLiftRaw Q i j q₀) (liftNeighborhood Q i j q₀) ∧
      ContMDiffOn 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) ∞
        (localRightRaw Q i j q₀) (liftNeighborhood Q i j q₀) ∧
      ∀ (y : M) (hy : y ∈ liftNeighborhood Q i j q₀),
        ∃ q r : unitary ℍ,
          (q : ℍ) = scalarLiftRaw Q i j q₀ y ∧
          (r : ℍ) = localRightRaw Q i j q₀ y ∧
          (fixedTransitionNormalizer leftLineStructure Q i j y
            hy.1.1 hy.1.2).1 =
            twoSidedIsometry q r := by
  obtain ⟨q₀, hx, hopen, hsmooth, _⟩ :=
    exists_local_scalar_lift Q leftLineStructure i j x hi hj
  refine ⟨q₀, hx, hopen, hsmooth, smooth_localRightRaw Q i j q₀, ?_⟩
  intro y hy
  obtain ⟨q, r, hq, hr, hreal, _, _⟩ := local_factors_clifford Q i j q₀ y hy
  exact ⟨q, r, hq, hr, hreal⟩

end
end QuaternionicSymmetry.FourDimensionalHalfSpinSmoothLocalFactors
