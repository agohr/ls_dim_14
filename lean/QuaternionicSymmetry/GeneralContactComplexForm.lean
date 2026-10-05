import QuaternionicSymmetry.GeneralContactDeterminantNonzero
import QuaternionicSymmetry.HolomorphicContactHamiltonianField

/-! The general contact quotient is complex-linear on its genuine complex
tangent fibers because its total-space map is holomorphic. -/
namespace QuaternionicSymmetry.GeneralContactComplexForm
open GeneralComplexContactData ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff
noncomputable section
variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
  {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
local notation "V" => ComplexTwistorModel n

def realForm (z : Z) : letI := C.charts; V →L[ℝ] ℂ := by
  letI := C.charts
  let f : V →ₗ[ℝ] ℂ := (C.theta z).comp (mfderiv 𝓘(ℝ,V) IR (id : Z → Z) z).toLinearMap
  exact f.toContinuousLinearMap

theorem realForm_holomorphic (z : Z) : letI := C.charts; ContDiff ℂ ∞ (realForm C z) := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.lineHolomorphic
  letI : IsManifold 𝓘(ℂ,V) (∞ + 1) Z := by simpa using C.complexManifold
  let T := tangentBundleCore 𝓘(ℂ,V) Z
  letI : T.IsContMDiff 𝓘(ℂ,V) ∞ := tangentBundleCore.isContMDiff
  letI : MemTrivializationAtlas (T.localTriv (achart V z)) := ⟨⟨achart V z,rfl⟩⟩
  letI : MemTrivializationAtlas (C.line.localTriv (C.line.indexAt z)) := ⟨⟨C.line.indexAt z,rfl⟩⟩
  have hinc : ContMDiff 𝓘(ℂ,V) (𝓘(ℂ,V)).tangent ∞
      (fun v : V => (⟨z,v⟩ : TangentBundle 𝓘(ℂ,V) Z)) := by
    apply ((T.localTriv (achart V z)).contMDiff_iff (fun _ => mem_chart_source V z)).mpr
    refine ⟨contMDiff_const,?_⟩
    change ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ (fun v : V => T.coordChange (achart V z) (achart V z) z v)
    simpa only [T.coordChange_self (achart V z) z (mem_chart_source V z)] using (contMDiff_id : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ (id : V → V))
  have h := C.thetaHolomorphic.comp hinc
  have hscalar := ((C.line.localTriv (C.line.indexAt z)).contMDiff_iff
    (fun _ => C.line.mem_baseSet_at z)).mp h |>.2
  change ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,ℂ) ∞
    (fun v : V => C.line.coordChange (C.line.indexAt z) (C.line.indexAt z) z (realForm C z v)) at hscalar
  simpa only [C.line.coordChange_self (C.line.indexAt z) z (C.line.mem_baseSet_at z)] using hscalar.contDiff

def complexForm (z : Z) : letI := C.charts; V →ₗ[ℂ] ℂ := by
  letI := C.charts
  exact (fderiv ℂ (realForm C z) 0).toLinearMap

theorem complexForm_apply (z : Z) (v : V) : letI := C.charts
    complexForm C z v = C.theta z (mfderiv 𝓘(ℝ,V) IR (id : Z → Z) z v) := by
  letI := C.charts
  have hd := (realForm_holomorphic C z).differentiable (by simp) (0 : V)
  have he := (hd.hasFDerivAt.restrictScalars ℝ).unique (realForm C z).hasFDerivAt
  exact congrArg (fun A : V →L[ℝ] ℂ => A v) he

end
end QuaternionicSymmetry.GeneralContactComplexForm
