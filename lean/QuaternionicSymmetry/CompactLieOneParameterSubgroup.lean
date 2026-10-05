import QuaternionicSymmetry.CompactVectorFieldFlow
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Every Lie algebra vector of a compact real Lie group integrates to an
actual continuous one-parameter subgroup, with the prescribed derivative.
The construction uses completeness and uniqueness of integral curves. -/
namespace QuaternionicSymmetry.CompactLieOneParameterSubgroup
open CompactVectorFieldFlow Function
open scoped Manifold ContDiff Topology
noncomputable section
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [CompactSpace G] [T2Space G]

local instance : ENat.LEInfty (minSmoothness ℝ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem field_c1 (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun g => (⟨g,mulInvariantVectorField v g⟩ : TangentBundle 𝓘(ℝ,E) G)) := by
  exact (contMDiff_mulInvariantVectorField v).of_le (by
    simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)

theorem left_invariant (v : GroupLieAlgebra 𝓘(ℝ,E) G) (g h : G) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x => g*x) h (mulInvariantVectorField v h) =
      mulInvariantVectorField v (g*h) := by
  have he : (fun x : G => (g*h)*x) = (fun x => g*x) ∘ (fun x => h*x) := by
    funext x; simp [mul_assoc]
  simp only [mulInvariantVectorField]
  rw [he, mfderiv_comp (I' := 𝓘(ℝ,E))]
  · rw [mul_one]
    rfl
  · exact (contMDiff_mul_left (I := 𝓘(ℝ,E)) (n := ∞)).mdifferentiableAt (by simp)
  · exact (contMDiff_mul_left (I := 𝓘(ℝ,E)) (n := ∞)).mdifferentiableAt (by simp)

theorem integral_mul_left (v : GroupLieAlgebra 𝓘(ℝ,E) G)
    {γ : ℝ → G} (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (g : G) :
    IsMIntegralCurve (fun t => g*γ t) (mulInvariantVectorField v) := by
  intro t
  have hg : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x) (γ t)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x) (γ t)) :=
    ((contMDiff_mul_left (I := 𝓘(ℝ,E)) (n := ∞)).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hh := hg.comp t (hγ t)
  apply hh.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro s
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, map_smul]
  rw [left_invariant]

def curve (v : GroupLieAlgebra 𝓘(ℝ,E) G) : ℝ → G :=
  flow (mulInvariantVectorField v) (field_c1 v) 1

@[simp] theorem curve_zero (v : GroupLieAlgebra 𝓘(ℝ,E) G) : curve v 0 = 1 :=
  flow_zero _ _ _

theorem curve_integral (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    IsMIntegralCurve (curve v) (mulInvariantVectorField v) := integral _ _ _

theorem flow_eq_mul (v : GroupLieAlgebra 𝓘(ℝ,E) G) (g : G) (t : ℝ) :
    flow (mulInvariantVectorField v) (field_c1 v) g t = g * curve v t := by
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (field_c1 v)
    (integral (mulInvariantVectorField v) (field_c1 v) g) (integral_mul_left v (curve_integral v) g)
    (t₀ := 0) (by simp)
  exact congrFun he t

theorem curve_add (v : GroupLieAlgebra 𝓘(ℝ,E) G) (s t : ℝ) :
    curve v (s+t) = curve v s * curve v t := by
  change flow (mulInvariantVectorField v) (field_c1 v) 1 (s+t) = _
  rw [add_comm s t, flow_add, flow_eq_mul]
  rfl

theorem curve_continuous (v : GroupLieAlgebra 𝓘(ℝ,E) G) : Continuous (curve v) :=
  (curve_integral v).continuous

theorem curve_derivative_zero (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (curve v) 0 (1 : ℝ) = v := by
  rw [(curve_integral v 0).mfderiv]
  change (1 : ℝ) • mulInvariantVectorField v (curve v 0) = v
  rw [one_smul, curve_zero]
  unfold mulInvariantVectorField
  have he : (fun x : G => 1*x) = id := funext one_mul
  rw [he, mfderiv_id]
  rfl

theorem curve_smul (v : GroupLieAlgebra 𝓘(ℝ,E) G) (a t : ℝ) :
    curve (G := G) (a • v) t = curve v (t*a) := by
  have hi : IsMIntegralCurve (fun s => curve v (s*a))
      (mulInvariantVectorField (a • v)) := by
    rw [mulInvariantVectorField_smul]
    exact (curve_integral v).comp_mul a
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (field_c1 (a • v))
    (curve_integral (G := G) (a • v)) hi (t₀ := 0) (by simp)
  exact congrFun he t

@[simp] theorem curve_neg (v : GroupLieAlgebra 𝓘(ℝ,E) G) (t : ℝ) :
    curve v (-t) = (curve v t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← curve_add, add_neg_cancel, curve_zero]


/-- The additive real parameter is written multiplicatively only to use
`MonoidHom`; the underlying curve and its group law are unchanged. -/
def hom (v : GroupLieAlgebra 𝓘(ℝ,E) G) : Multiplicative ℝ →* G where
  toFun t := curve v (Multiplicative.toAdd t)
  map_one' := curve_zero v
  map_mul' s t := curve_add v (Multiplicative.toAdd s) (Multiplicative.toAdd t)

@[simp] theorem hom_apply (v : GroupLieAlgebra 𝓘(ℝ,E) G) (t : ℝ) :
    hom v (Multiplicative.ofAdd t) = curve v t := rfl

theorem continuous_hom (v : GroupLieAlgebra 𝓘(ℝ,E) G) : Continuous (hom v) :=
  (curve_continuous v).comp continuous_toAdd

end
end QuaternionicSymmetry.CompactLieOneParameterSubgroup
