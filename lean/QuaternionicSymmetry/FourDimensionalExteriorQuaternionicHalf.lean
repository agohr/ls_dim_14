import QuaternionicSymmetry.FourDimensionalExteriorHodge

/-! In any actual unit quaternionic frame, the positive Hodge half of genuine
exterior two-covectors is exactly the metric two-form image of the native
quaternionic endomorphism submodule. -/
namespace QuaternionicSymmetry.FourDimensionalExteriorQuaternionicHalf

open Module FourDimensionalExteriorHodge FourDimensionalCoordinateHodge
open FourDimensionalQuaternionicHodgeFrame
open FourDimensionalQuaternionicPositiveSubmodule
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def clmToLinear : (V →L[ℝ] V) →ₗ[ℝ] (V →ₗ[ℝ] V) where
  toFun A := A.toLinearMap
  map_add' A B := rfl
  map_smul' c A := rfl

def operatorForm (b : Basis (Fin 4) ℝ V) :
    (V →L[ℝ] V) →ₗ[ℝ] TwoForm V :=
  (HyperholomorphicExterior.form b).comp clmToLinear

theorem operatorForm_basis_independent
    (b c : Basis (Fin 4) ℝ V) : operatorForm b = operatorForm c := by
  apply LinearMap.ext
  intro A
  change HyperholomorphicExterior.form b A.toLinearMap =
    HyperholomorphicExterior.form c A.toLinearMap
  exact HyperholomorphicExterior.form_basis_independent
    b c A.toLinearMap

def skewContinuousEndomorphisms : Submodule ℝ (V →L[ℝ] V) where
  carrier := {A | ∀ v w, inner ℝ (A v) w = -inner ℝ v (A w)}
  zero_mem' := by intro v w; simp
  add_mem' := by
    intro A B hA hB v w
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
      hA v w, hB v w]
    ring
  smul_mem' := by
    intro c A hA v w
    simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left,
      real_inner_smul_right, hA v w]
    ring

theorem quaternionicSpan_skew (Q : QuaternionicStructure V)
    (A : V →L[ℝ] V) (hA : A ∈ quaternionicSpan Q) :
    ∀ v w, inner ℝ (A v) w = -inner ℝ v (A w) := by
  have hle : quaternionicSpan Q ≤ skewContinuousEndomorphisms := by
    apply Submodule.span_le.mpr
    rintro A ⟨t, rfl⟩
    change ∀ v w, inner ℝ (quaternionicGenerator Q t v) w =
      -inner ℝ v (quaternionicGenerator Q t w)
    fin_cases t
    · exact Q.I_skew
    · exact Q.J_skew
    · exact Q.K_skew
  exact hle hA

def positiveExteriorHalf (b : OrthonormalBasis (Fin 4) ℝ V) :
    Submodule ℝ (TwoForm V) :=
  LinearMap.ker (frameStar b - LinearMap.id)

theorem mem_positiveExteriorHalf (b : OrthonormalBasis (Fin 4) ℝ V)
    (α : TwoForm V) :
    α ∈ positiveExteriorHalf b ↔ frameStar b α = α := by
  simp [positiveExteriorHalf, LinearMap.mem_ker, sub_eq_zero]

theorem positiveExteriorHalf_eq_quaternionicFormImage
    (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    positiveExteriorHalf (frameBasis Q hdim v hv) =
      (quaternionicSpan Q).map
        (operatorForm (frameBasis Q hdim v hv).toBasis) := by
  let b := frameBasis Q hdim v hv
  apply Submodule.ext
  intro α
  constructor
  · intro hα
    have hstar := (mem_positiveExteriorHalf b α).mp hα
    have hcoords : FourDimensionalCoordinateHodge.star
        (coordinates b.toBasis α) = coordinates b.toBasis α := by
      rw [← coordinates_frameStar, hstar]
    have hspan : coordinates b.toBasis α ∈
        (quaternionicSpan Q).map (twoCoordsLinear b) := by
      rw [← positiveHalf_eq_quaternionicSpan_image Q hdim v hv]
      exact (mem_positiveHalf _).mpr hcoords
    obtain ⟨A,hA,hAc⟩ := hspan
    refine ⟨A,hA,?_⟩
    apply (coordinateEquiv b.toBasis).injective
    change coordinates b.toBasis
      (HyperholomorphicExterior.form b.toBasis A.toLinearMap) =
      coordinates b.toBasis α
    rw [coordinates_operatorForm b A.toLinearMap (quaternionicSpan_skew Q A hA)]
    exact hAc
  · rintro ⟨A,hA,rfl⟩
    apply (mem_positiveExteriorHalf b _).mpr
    apply (coordinateEquiv b.toBasis).injective
    change coordinates b.toBasis (frameStar b
      (HyperholomorphicExterior.form b.toBasis A.toLinearMap)) =
      coordinates b.toBasis
        (HyperholomorphicExterior.form b.toBasis A.toLinearMap)
    rw [coordinates_frameStar,
      coordinates_operatorForm b A.toLinearMap (quaternionicSpan_skew Q A hA)]
    have hAc : twoCoordsLinear b A ∈
        (quaternionicSpan Q).map (twoCoordsLinear b) :=
      ⟨A,hA,rfl⟩
    have hp : twoCoordsLinear b A ∈ positiveHalf := by
      rw [positiveHalf_eq_quaternionicSpan_image Q hdim v hv]
      exact hAc
    exact (mem_positiveHalf _).mp hp

theorem quaternionicPositiveHalf_frame_independent
    (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v w : V)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    positiveExteriorHalf (frameBasis Q hdim v hv) =
      positiveExteriorHalf (frameBasis Q hdim w hw) := by
  rw [positiveExteriorHalf_eq_quaternionicFormImage Q hdim v hv,
    positiveExteriorHalf_eq_quaternionicFormImage Q hdim w hw]
  rw [operatorForm_basis_independent]

end
end QuaternionicSymmetry.FourDimensionalExteriorQuaternionicHalf
