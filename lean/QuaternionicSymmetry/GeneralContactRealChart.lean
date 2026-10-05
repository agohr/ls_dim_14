import QuaternionicSymmetry.GeneralComplexContactSections
import QuaternionicSymmetry.HolomorphicLineOneFormCoordinates
import QuaternionicSymmetry.ComplexManifoldDerivativeScalarRestriction

/-! Exact real derivatives of the complex coordinate charts of contact data. -/
namespace QuaternionicSymmetry.GeneralContactRealChart
open GeneralComplexContactData ManifoldTwistorLeBrunComplexAtlas
  HolomorphicLineOneFormCoordinates ComplexManifoldDerivativeScalarRestriction
open scoped Manifold ContDiff
noncomputable section
variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
  {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
local notation "V" => ComplexTwistorModel n

/-- The derivative of the smooth atlas comparison is invertible. -/
theorem realId_isInvertible (z : Z) :
    letI := C.charts
    letI := C.complexManifold
    (mfderiv 𝓘(ℝ,V) IR (id : Z → Z) z).IsInvertible := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.realManifold
  have hto := C.smoothToReal.mdifferentiableAt (by simp) (x := z)
  have hfrom := C.smoothFromReal.mdifferentiableAt (by simp) (x := z)
  have h₁ := C.realId_deriv_comp_inverse z
  have h₂ : (mfderiv IR 𝓘(ℝ,V) (id : Z → Z) z).comp
      (mfderiv 𝓘(ℝ,V) IR (id : Z → Z) z) = ContinuousLinearMap.id ℝ V := by
    simpa only [Function.comp_id, mfderiv_id] using (mfderiv_comp z hfrom hto).symm
  exact ContinuousLinearMap.IsInvertible.of_inverse h₁ h₂

theorem chartInverse_real_contMDiffAt (i : letI := C.charts; atlas V Z) (y : V) (hy : y ∈ i.1.target) :
    letI := C.charts
    letI := C.complexManifold
    ContMDiffAt 𝓘(ℝ,V) IR ∞ i.1.symm y := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.realManifold
  have h := contMDiffAt_symm_of_mem_maximalAtlas
    (I := 𝓘(ℝ,V)) (n := ∞) (IsManifold.subset_maximalAtlas i.2) hy
  exact C.smoothToReal.contMDiffAt.comp y h

theorem chartInverse_real_derivative (i : letI := C.charts; atlas V Z) (y : V) (hy : y ∈ i.1.target) :
    letI := C.charts
    letI := C.complexManifold
    mfderiv 𝓘(ℝ,V) IR i.1.symm y =
      (mfderiv 𝓘(ℝ,V) IR (id : Z → Z) (i.1.symm y)).comp
        (((tangentBundleCore 𝓘(ℂ,V) Z).coordChange i (achart V (i.1.symm y))
          (i.1.symm y)).restrictScalars ℝ) := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.realManifold
  have hr := (contMDiffAt_symm_of_mem_maximalAtlas
    (I := 𝓘(ℝ,V)) (n := ∞) (IsManifold.subset_maximalAtlas i.2) hy).mdifferentiableAt (by simp)
  have hc := (contMDiffAt_symm_of_mem_maximalAtlas
    (I := 𝓘(ℂ,V)) (n := ∞) (IsManifold.subset_maximalAtlas i.2) hy).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp y
    (C.smoothToReal.mdifferentiableAt (by simp) (x := i.1.symm y)) hr
  simpa only [Function.id_comp, mfderiv_real_eq_complex hr hc,
    mfderiv_chart_symm_eq_coordChange i y hy] using hcomp

theorem chartInverse_real_isInvertible (i : letI := C.charts; atlas V Z) (y : V) (hy : y ∈ i.1.target) :
    letI := C.charts
    letI := C.complexManifold
    (mfderiv 𝓘(ℝ,V) IR i.1.symm y).IsInvertible := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.realManifold
  rw [chartInverse_real_derivative C i y hy]
  apply (realId_isInvertible C (i.1.symm y)).comp
  let T := tangentBundleCore 𝓘(ℂ,V) Z
  let j := achart V (i.1.symm y)
  have hi : i.1.symm y ∈ T.baseSet i := i.1.map_target hy
  have hj : i.1.symm y ∈ T.baseSet j := mem_chart_source V (i.1.symm y)
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (T.coordChange j i (i.1.symm y)).restrictScalars ℝ)
  · apply ContinuousLinearMap.ext
    intro v
    exact (T.coordChange_comp j i j _ ⟨⟨hj,hi⟩,hj⟩ v).trans (T.coordChange_self j _ hj v)
  · apply ContinuousLinearMap.ext
    intro v
    exact (T.coordChange_comp i j i _ ⟨⟨hi,hj⟩,hi⟩ v).trans (T.coordChange_self i _ hi v)

end
end QuaternionicSymmetry.GeneralContactRealChart
