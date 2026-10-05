import QuaternionicSymmetry.GeneralContactRealChart
import QuaternionicSymmetry.ContactRealLeviCoordinates
import QuaternionicSymmetry.HolomorphicContactDeterminantGauge

/-! The actual real Levi hypothesis makes the holomorphic contact determinant
nowhere zero. The complex-linear form is required to be the actual transported
real contact form, not an unrelated bundle map. -/
namespace QuaternionicSymmetry.GeneralContactDeterminantNonzero
open GeneralComplexContactData ManifoldTwistorLeBrunComplexAtlas GeneralContactRealChart
  HolomorphicLineOneFormCoordinates HolomorphicContactDeterminantDensity
  ContactExteriorDerivativeCalculus ContactDeterminantAlgebra ContactRealLeviCoordinates
open scoped Manifold ContDiff Topology
noncomputable section
variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
  {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
local notation "V" => ComplexTwistorModel n

/-- Nonvanishing for the genuine contact form on every common chart. -/
theorem density_ne_zero (θ : Z → V →ₗ[ℂ] ℂ)
    (hθ : letI := C.charts; ∀ z v, θ z v = C.theta z
      (mfderiv 𝓘(ℝ,V) IR (id : Z → Z) z v)) :
    letI := C.charts
    letI := C.complexManifold
    letI := C.lineHolomorphic
    ∀ (i : atlas V Z) (a : C.Index) (z : Z), z ∈ i.1.source → z ∈ C.line.baseSet a →
      density C.line θ i a z ≠ 0 := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.realManifold
  letI := C.lineHolomorphic
  intro i a z hi ha
  let x := i.1 z
  let F : V → Z := i.1.symm
  let A := coordinateForm C.line θ i a
  let c : V → ℂ →ₗ[ℝ] ℂ := fun y =>
    (C.line.coordChange (C.line.indexAt (F y)) a (F y)).toLinearMap.restrictScalars ℝ
  have hFx : F x = z := i.1.left_inv hi
  have hx : x ∈ i.1.target := i.1.map_source hi
  have hhol : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TangentBundle 𝓘(ℂ,V) Z =>
        (⟨t.1, θ t.1 t.2⟩ : Bundle.TotalSpace ℂ C.line.Fiber)) := by
    simpa only [hθ] using C.thetaHolomorphic
  have hA := (coordinateForm_contDiffAt C.line θ hhol i a z hi ha).differentiableAt (by simp)
  have hF := chartInverse_real_contMDiffAt C i x hx
  have hInv : ∀ᶠ y in 𝓝 x, (mfderiv 𝓘(ℝ,V) IR F y).IsInvertible := by
    filter_upwards [i.1.open_target.mem_nhds hx] with y hy
    exact chartInverse_real_isInvertible C i y hy
  have hline : ∀ᶠ y in 𝓝 x, F y ∈ C.line.baseSet a :=
    (i.1.continuousAt_symm hx).eventually (by
      change C.line.baseSet a ∈ 𝓝 (F x)
      rw [hFx]
      exact (C.line.isOpen_baseSet a).mem_nhds ha)
  have hcbij (y : V) (hy : F y ∈ C.line.baseSet a) : Function.Bijective (c y) := by
    exact ((C.line.localTriv a).linearEquivAt (R := ℂ) (F y) hy).bijective
  have hc : ∀ᶠ y in 𝓝 x, Function.Injective (c y) := by
    filter_upwards [hline] with y hy
    exact (hcbij y hy).injective
  have hform : ∀ᶠ y in 𝓝 x, ∀ v, A y v = c y
      (C.theta (F y) (mfderiv 𝓘(ℝ,V) IR F y v)) := by
    filter_upwards [i.1.open_target.mem_nhds hx] with y hy
    intro v
    change C.line.coordChange (C.line.indexAt (F y)) a (F y)
      (θ (F y) ((tangentBundleCore 𝓘(ℂ,V) Z).coordChange i (achart V (F y)) (F y) v)) = _
    rw [hθ, chartInverse_real_derivative C i y hy]
    rfl
  have hlevi : ∀ u : TangentSpace IR (F x), C.theta (F x) u = 0 → u ≠ 0 →
      ∃ U : Set Z, IsOpen U ∧ F x ∈ U ∧
      ∃ X Y : ∀ y : Z, TangentSpace IR y,
        ContMDiffOn IR IR.tangent ∞ (fun y => (⟨y,X y⟩ : TangentBundle IR Z)) U ∧
        ContMDiffOn IR IR.tangent ∞ (fun y => (⟨y,Y y⟩ : TangentBundle IR Z)) U ∧
        (∀ y ∈ U, C.theta y (X y) = 0) ∧ (∀ y ∈ U, C.theta y (Y y) = 0) ∧
        X (F x) = u ∧ C.theta (F x) (VectorField.mlieBracket IR X Y (F x)) ≠ 0 := by
    intro u hu hune
    exact C.leviNondegenerate (F x) ⟨u,hu⟩ (by
      intro h
      apply hune
      exact congrArg Subtype.val h)
  have hker := nondegenerate_of_real_levi C.theta F A c x hA hF hInv hc hform hlevi
  have hsurj : Function.Surjective (A x) := by
    intro w
    obtain ⟨s,hs⟩ := (hcbij x (by simpa only [hFx] using ha)).surjective w
    obtain ⟨v,hv⟩ := C.thetaSurjective (F x) s
    obtain ⟨u,hu⟩ := hInv.self_of_nhds.surjective v
    refine ⟨u, ?_⟩
    rw [hform.self_of_nhds u, hu, hv, hs]
  exact border_det_ne_zero ((Module.finBasis ℂ V).prod (Module.Basis.singleton Unit ℂ))
    (A x).toLinearMap (exteriorDerivative A x) hsurj (exteriorDerivative_alt A x) hker

end
end QuaternionicSymmetry.GeneralContactDeterminantNonzero
