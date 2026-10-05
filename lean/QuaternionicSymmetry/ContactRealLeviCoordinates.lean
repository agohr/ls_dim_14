import QuaternionicSymmetry.ContactExteriorDerivativeCalculus
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! The complex exterior derivative also computes the Levi bracket of real
smooth horizontal fields, and is natural under genuine real chart maps. -/
namespace QuaternionicSymmetry.ContactRealLeviCoordinates
open ContactExteriorDerivativeCalculus Filter VectorField
open scoped Manifold ContDiff Topology
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem exteriorDerivative_real_horizontal
    (a : V → V →L[ℂ] ℂ) (X Y : V → V) (x : V)
    (ha : DifferentiableAt ℂ a x) (hX : DifferentiableAt ℝ X x)
    (hY : DifferentiableAt ℝ Y x)
    (haX : (fun y => a y (X y)) =ᶠ[𝓝 x] fun _ => 0)
    (haY : (fun y => a y (Y y)) =ᶠ[𝓝 x] fun _ => 0) :
    exteriorDerivative a x (X x) (Y x) = -a x (lieBracket ℝ X Y x) := by
  let A : V → V →L[ℝ] ℂ := fun y => (a y).restrictScalars ℝ
  let R := ContinuousLinearMap.restrictScalarsL ℂ V ℂ ℝ ℝ
  have hA : DifferentiableAt ℝ A x :=
    R.differentiableAt.comp x (ha.restrictScalars ℝ)
  have hd : fderiv ℝ A x = R.comp ((fderiv ℂ a x).restrictScalars ℝ) := by
    have h : fderiv ℝ A x = R.comp (fderiv ℝ a x) :=
      R.hasFDerivAt.comp x (ha.restrictScalars ℝ).hasFDerivAt |>.fderiv
    rw [h, ha.fderiv_restrictScalars ℝ]
  have hx := congrArg (fun T : V →L[ℝ] ℂ => T (Y x)) haX.fderiv_eq
  have hy := congrArg (fun T : V →L[ℝ] ℂ => T (X x)) haY.fderiv_eq
  change (fderiv ℝ (fun y => A y (X y)) x) (Y x) = _ at hx
  change (fderiv ℝ (fun y => A y (Y y)) x) (X x) = _ at hy
  rw [fderiv_clm_apply hA hX, fderiv_const_apply, hd] at hx
  rw [fderiv_clm_apply hA hY, fderiv_const_apply, hd] at hy
  change a x (fderiv ℝ X x (Y x)) + fderiv ℂ a x (Y x) (X x) = 0 at hx
  change a x (fderiv ℝ Y x (X x)) + fderiv ℂ a x (X x) (Y x) = 0 at hy
  simp only [exteriorDerivative_apply, lieBracket, map_sub]
  linear_combination hy - hx

section Manifold
variable [CompleteSpace V]
  {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]

/-- Real bracket nondegeneracy implies nondegeneracy of the complex
coordinate exterior derivative. All coordinate transports here are the
actual manifold derivative and its inverse. -/
theorem nondegenerate_of_real_levi
    (θ : ∀ z : Z, TangentSpace IR z →ₗ[ℝ] ℂ)
    (F : V → Z) (a : V → V →L[ℂ] ℂ) (c : V → ℂ →ₗ[ℝ] ℂ) (x : V)
    (ha : DifferentiableAt ℂ a x)
    (hF : ContMDiffAt 𝓘(ℝ,V) IR ∞ F x)
    (hInv : ∀ᶠ y in 𝓝 x, (mfderiv 𝓘(ℝ,V) IR F y).IsInvertible)
    (hc : ∀ᶠ y in 𝓝 x, Function.Injective (c y))
    (hform : ∀ᶠ y in 𝓝 x, ∀ v, a y v = c y (θ (F y) (mfderiv 𝓘(ℝ,V) IR F y v)))
    (hlevi : ∀ u : TangentSpace IR (F x), θ (F x) u = 0 → u ≠ 0 →
      ∃ U : Set Z, IsOpen U ∧ F x ∈ U ∧
      ∃ X Y : ∀ z : Z, TangentSpace IR z,
        ContMDiffOn IR IR.tangent ∞ (fun z => (⟨z,X z⟩ : TangentBundle IR Z)) U ∧
        ContMDiffOn IR IR.tangent ∞ (fun z => (⟨z,Y z⟩ : TangentBundle IR Z)) U ∧
        (∀ z ∈ U, θ z (X z) = 0) ∧ (∀ z ∈ U, θ z (Y z) = 0) ∧
        X (F x) = u ∧ θ (F x) (mlieBracket IR X Y (F x)) ≠ 0) :
    ∀ u, a x u = 0 → (∀ v, a x v = 0 → exteriorDerivative a x u v = 0) → u = 0 := by
  letI : IsManifold IR (minSmoothness ℝ 2) Z := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using (inferInstance : IsManifold IR 2 Z)
  intro u hau hdeg
  by_contra hu
  have hInvx := hInv.self_of_nhds
  have hcx := hc.self_of_nhds
  have hfx := hform.self_of_nhds
  have hθu : θ (F x) (mfderiv 𝓘(ℝ,V) IR F x u) = 0 := by
    apply hcx
    rw [← hfx, hau, map_zero]
  have hdu : mfderiv 𝓘(ℝ,V) IR F x u ≠ 0 := by
    intro he
    apply hu
    exact hInvx.injective (he.trans (map_zero _).symm)
  obtain ⟨U,hU,hxU,X,Y,hX,hY,hθX,hθY,hXu,hbr⟩ := hlevi _ hθu hdu
  let P := mpullback 𝓘(ℝ,V) IR F X
  let Q := mpullback 𝓘(ℝ,V) IR F Y
  have hXx := (hX (F x) hxU).contMDiffAt (hU.mem_nhds hxU)
  have hYx := (hY (F x) hxU).contMDiffAt (hU.mem_nhds hxU)
  have hP := hXx.mpullback_vectorField_preimage hF hInvx (by simp : ∞ + 1 ≤ ∞)
  have hQ := hYx.mpullback_vectorField_preimage hF hInvx (by simp : ∞ + 1 ≤ ∞)
  have hPdiff : DifferentiableAt ℝ P x := by
    exact (contMDiffAt_vectorSpace_iff_contDiffAt.mp hP).differentiableAt (by simp)
  have hQdiff : DifferentiableAt ℝ Q x := by
    exact (contMDiffAt_vectorSpace_iff_contDiffAt.mp hQ).differentiableAt (by simp)
  have hnearU : ∀ᶠ y in 𝓝 x, F y ∈ U := hF.continuousAt.eventually (hU.mem_nhds hxU)
  have hPa : (fun y => a y (P y)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hform, hInv, hnearU] with y hy hinv hyU
    rw [hy]
    change c y (θ (F y) (mfderiv 𝓘(ℝ,V) IR F y
      ((mfderiv 𝓘(ℝ,V) IR F y).inverse (X (F y))))) = 0
    rw [hinv.self_apply_inverse, hθX _ hyU, map_zero]
  have hQa : (fun y => a y (Q y)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hform, hInv, hnearU] with y hy hinv hyU
    rw [hy]
    change c y (θ (F y) (mfderiv 𝓘(ℝ,V) IR F y
      ((mfderiv 𝓘(ℝ,V) IR F y).inverse (Y (F y))))) = 0
    rw [hinv.self_apply_inverse, hθY _ hyU, map_zero]
  have hPu : P x = u := by
    change (mfderiv 𝓘(ℝ,V) IR F x).inverse (X (F x)) = u
    rw [hXu, hInvx.inverse_apply_self]
  have hlev := exteriorDerivative_real_horizontal a P Q x ha hPdiff hQdiff hPa hQa
  have hzero := hdeg (Q x) hQa.self_of_nhds
  rw [← hPu] at hzero
  rw [hzero] at hlev
  have hB : a x (lieBracket ℝ P Q x) = 0 := neg_eq_zero.mp hlev.symm
  have hnat := mpullback_mlieBracket
    (hXx.mdifferentiableAt (by simp)) (hYx.mdifferentiableAt (by simp)) hF
    (by simp only [minSmoothness_of_isRCLikeNormedField]; decide : minSmoothness ℝ 2 ≤ ∞)
  have hnat' : (mfderiv 𝓘(ℝ,V) IR F x).inverse (mlieBracket IR X Y (F x)) =
      lieBracket ℝ P Q x := by
    simpa only [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin,
      lieBracketWithin_univ, P, Q, mpullback_apply] using hnat
  rw [← hnat', hfx, hInvx.self_apply_inverse] at hB
  exact hbr (hcx (hB.trans (map_zero _).symm))

end Manifold
end
end QuaternionicSymmetry.ContactRealLeviCoordinates
