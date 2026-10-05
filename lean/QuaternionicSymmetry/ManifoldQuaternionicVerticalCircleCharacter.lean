import QuaternionicSymmetry.ManifoldQuaternionicVerticalComplexCharacter
import QuaternionicSymmetry.ManifoldQuaternionicFixedPointCoefficientContinuous
import QuaternionicSymmetry.ManifoldQuaternionicVerticalWeightKernel
import QuaternionicSymmetry.TorusCharacterInput

/-! The actual vertical complex isotropy is a continuous circle character.
Its integer weight is derived from the registered general circle-character
theorem, not assumed as a property of the manifold. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicVerticalComplexCharacter
open ManifoldQuaternionicFixedPointCoefficientContinuous
open ManifoldQuaternionicTwistorIsotropyWeight
open ManifoldQuaternionicVerticalWeightKernel
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIsometryTopology
open ManifoldRiemannianIsometryLieInput
open ManifoldTwistorSphereCore ManifoldTwistorSphereBundle
open ManifoldTwistorVerticalComplex ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff Matrix
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem continuous_verticalScalar (hR3 : IsometryLieSource.{0,0})
    (z : SphereBundleTotal Q) :
    Continuous (verticalScalar Q z) := by
  let a := coefficientSphereHomeomorph.symm z.2
  let S := MulAction.stabilizer (QuaternionicIsometries Q) z
  letI := coefficientVerticalComplexModule a
  letI : Nontrivial (verticalSubmodule a) :=
    Module.nontrivial_of_finrank_pos (by
      rw [coefficientVerticalComplex_finrank Q z]
      omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : verticalSubmodule a)
  have hv' : v.1 ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  have hdot : v.1 ⬝ᵥ v.1 ≠ 0 := by
    intro h
    exact hv' (dotProduct_self_eq_zero.mp h)
  have hx : z.1 ∈ fixedPoints Q S := by
    intro f hf
    exact isotropy_fixes_base Q z ⟨f,hf⟩
  have hcoeff : Continuous (fun f : S =>
      (isotropyVerticalRepresentation Q z f v).1) :=
    continuous_coefficientAction_fixed Q hR3 S z.1 hx v.1
  have hrealFormula (f : S) :
      (verticalScalar Q z f).re =
        ((isotropyVerticalRepresentation Q z f v).1 ⬝ᵥ v.1) /
          (v.1 ⬝ᵥ v.1) :=
    (eq_div_iff hdot).mpr (verticalScalar_re_mul_dot Q z f v)
  have himagFormula (f : S) :
      (verticalScalar Q z f).im =
        ((isotropyVerticalRepresentation Q z f v).1 ⬝ᵥ (a.1 ⨯₃ v.1)) /
          (v.1 ⬝ᵥ v.1) :=
    (eq_div_iff hdot).mpr (verticalScalar_im_mul_dot Q z f v)
  have hreal : Continuous (fun f : S => (verticalScalar Q z f).re) := by
    simp_rw [hrealFormula]
    exact (hcoeff.dotProduct continuous_const).div_const _
  have himag : Continuous (fun f : S => (verticalScalar Q z f).im) := by
    simp_rw [himagFormula]
    exact (hcoeff.dotProduct continuous_const).div_const _
  have hrepr : (fun f : S => verticalScalar Q z f) =
      (fun f : S => ((verticalScalar Q z f).re : ℂ) +
        (verticalScalar Q z f).im * Complex.I) := by
    funext f
    exact (Complex.re_add_im _).symm
  change Continuous (fun f : S => verticalScalar Q z f)
  rw [hrepr]
  exact (Complex.continuous_ofReal.comp hreal).add
    ((Complex.continuous_ofReal.comp himag).mul continuous_const)

def verticalScalarCircle (z : SphereBundleTotal Q)
    (f : MulAction.stabilizer (QuaternionicIsometries Q) z) : Circle :=
  ⟨verticalScalar Q z f, by
    have hnormSq := verticalScalar_normSq_eq_one Q z f
    have hnorm : ‖verticalScalar Q z f‖ = 1 := by
      have hsq : ‖verticalScalar Q z f‖ ^ 2 = 1 := by
        simpa only [Complex.normSq_eq_norm_sq] using hnormSq
      nlinarith [norm_nonneg (verticalScalar Q z f)]
    exact mem_sphere_zero_iff_norm.mpr hnorm⟩

/-- The genuine vertical derivative at a fixed twistor point, as a continuous
unit-circle character of its full smooth quaternionic-isometry stabilizer. -/
def verticalCircleCharacter (hR3 : IsometryLieSource.{0,0})
    (z : SphereBundleTotal Q) :
    MulAction.stabilizer (QuaternionicIsometries Q) z →ₜ* Circle where
  toMonoidHom := {
    toFun := verticalScalarCircle Q z
    map_one' := by
      apply Circle.ext
      exact verticalScalar_one Q z
    map_mul' := by
      intro f g
      apply Circle.ext
      exact verticalScalar_mul Q z f g }
  continuous_toFun :=
    Continuous.subtype_mk (continuous_verticalScalar Q hR3 z) _

/-- Restrict an actual continuous torus action to a twistor point fixed by
every torus element. The subgroup topology is inherited from the genuine
compact-open topology of quaternionic isometries. -/
def torusToTwistorIsotropy {r : ℕ} (A : ContinuousTorusAction Q r)
    (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z) :
    Torus r →ₜ* MulAction.stabilizer (QuaternionicIsometries Q) z where
  toMonoidHom := {
    toFun := fun t => ⟨A.representation t, hz t⟩
    map_one' := by apply Subtype.ext; exact map_one A.representation
    map_mul' := by intro s t; apply Subtype.ext; exact map_mul A.representation s t }
  continuous_toFun := Continuous.subtype_mk
    (continuous_representation_of_action Q A.representation A.continuous_action) _

/-- Continuous unitary vertical isotropy character of the actual torus
action at an actual fixed twistor point. -/
def torusVerticalCircleCharacter (hR3 : IsometryLieSource.{0,0})
    {r : ℕ} (A : ContinuousTorusAction Q r)
    (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z) :
    Torus r →ₜ* Circle :=
  (verticalCircleCharacter Q hR3 z).comp (torusToTwistorIsotropy Q A z hz)

/-- BG-T1 quantizes the actual continuous vertical character. The integer
weight may be zero; nonzero weight requires a separate geometric argument. -/
theorem exists_actual_vertical_weight (hR3 : IsometryLieSource.{0,0})
    (hCircle : TorusCharacterInput.CircleCharacterSource)
    {r : ℕ} (A : ContinuousTorusAction Q r)
    (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z) :
    ∃ μ : Fin r → ℤ, HasVerticalWeight Q A z hz μ := by
  obtain ⟨μ, hμ⟩ := TorusCharacterInput.exists_weightCharacter hCircle
    (torusVerticalCircleCharacter Q hR3 A z hz)
  refine ⟨μ, ?_⟩
  intro t v
  have hscalar : verticalScalar Q z ⟨A.representation t, hz t⟩ =
      ((weightCharacter μ t : Circle) : ℂ) :=
    by simpa only [torusVerticalCircleCharacter, verticalCircleCharacter,
      torusToTwistorIsotropy] using
      congrArg (fun c : Circle => (c : ℂ)) (hμ t)
  rw [isotropyVerticalRepresentation_eq_verticalScalar, hscalar]
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicVerticalCircleCharacter
