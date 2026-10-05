import QuaternionicSymmetry.ManifoldQuaternionicImmersionCharts
import QuaternionicSymmetry.QuaternionicImmersionHessian
import QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
import QuaternionicSymmetry.ManifoldQuaternionicInducedLocalCoefficientJointSmooth

/-! Smooth isometric quaternionic immersions are totally geodesic for the
supplied metric, torsion-free quaternionic connections. This proves the
actual all-chart Hessian condition internally. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionTotalGeodesy
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicInducedTotalGeodesy
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicImmersionCharts
open ManifoldQuaternionicAdjointConnection
open ManifoldQuaternionicRankThreeOrthogonal
open ManifoldQuaternionicInducedLocalCoefficientJointSmooth
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ImmersionHessianCalculus QuaternionicImmersionHessian
open QuaternionicSecondFundamentalAlgebra
open Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem isTotallyGeodesic
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
    (ι : N → M) (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (hR : IsInducedQuaternionicGeometry P R ι)
    (DP : CompatibleTangentConnection P.tangent)
    (DR : CompatibleTangentConnection R.tangent) :
    IsTotallyGeodesic P R ι DP DR := by
  intro q p y hy u v
  let A := adaptedRectangularDerivative P R ι q p
  let G := localBaseMap (E := E) (F := F) ι q p
  let S := solder R.tangent q
  let T := solder P.tangent p
  let U := coordinateInverse R.tangent q y
  let SR := R.tangent.reduction.Q (achart F q)
  let SP := P.tangent.reduction.Q (achart E p)
  let C : F → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := fun z =>
    localCoefficientCLM P R ι hι hR (achart F q) (achart E p)
      ((extChartAt 𝓘(ℝ,F) q).symm z)
  let H : F → F → E := hessian A G y (DP.form p (G y)) (DR.form q y)
  let B : F → F → E := fun a b => H (U a) b
  have htarget : G y ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source hy.2
  have hA := adapted_differentiableAt P R ι hSmooth q p y hy
  have hG := (contDiffAt_infty.mp (localBaseMap_contDiffAt ι hSmooth q p y hy)) 2
  have hS := (solder_contDiffAt R.tangent q y hy.1).differentiableAt (by norm_num)
  have hT := (solder_contDiffAt P.tangent p (G y) htarget).differentiableAt (by norm_num)
  have hnear := overlap_eventually ι hSmooth q p y hy
  have hiso : ∀ᶠ z in 𝓝 y, ∀ a b, inner ℝ (A z a) (A z b) = inner ℝ a b := by
    filter_upwards [hnear] with z hz
    exact adapted_inner P R ι hR q p z hz
  have hInter : ∀ᶠ z in 𝓝 y, ∀ a b,
      A z (synth SR a b) = synth SP (C z a) (A z b) := by
    filter_upwards [hnear] with z hz
    exact adaptedRectangularDerivative_intertwines_on_overlap P R ι hι hR q p z hz
  have hC : DifferentiableAt ℝ C y :=
    coefficient_differentiableAt SR SP A C y hA hiso hInter
  have hcov : (fun z => (A z).comp (S z)) =ᶠ[𝓝 y]
      (fun z => (T (G z)).comp (fderiv ℝ G z)) := by
    filter_upwards [hnear] with z hz
    exact solder_covariance P R ι hSmooth q p z hz
  have hSU (a : F) : S y (U a) = a :=
    congrArg (fun L : F →L[ℝ] F => L a) (coordinateInverse_right R.tangent q y hy.1)
  have hUS (a : F) : U (S y a) = a :=
    congrArg (fun L : F →L[ℝ] F => L a) (coordinateInverse_left R.tangent q y hy.1)
  have hsym (a b : F) : B a b = B b a := by
    have h := hessian_symmetric A S T G y (DP.form p (G y)) (DR.form q y)
      hA hS hT hG hcov (fun a b => DP.torsion p (G y) a b htarget)
      (fun a b => DR.torsion q y a b hy.1) (U a) (U b)
    change H (U a) (S y (U b)) = H (U b) (S y (U a)) at h
    simpa only [hSU] using h
  have hmetric (a b c : F) : inner ℝ (B a b) (A y c) + inner ℝ (A y b) (B a c) = 0 :=
    hessian_metric A G y (DP.form p (G y)) (DR.form q y) hA hiso
      (fun a b c => DP.metric p (G y) a b c htarget)
      (fun a b c => DR.metric q y a b c hy.1) (U a) b c
  have hnormal := normal_of_metric_and_symmetry (A y) B hsym hmetric
  have hAt := hInter.self_of_nhds
  have hAi := adaptedRectangularDerivative_injective_on_overlap P R ι hι q p y hy
  have hCi : Function.Injective (C y) := by
    intro a b hab
    have heq : synth SR a = synth SR b := by
      ext w
      apply hAi
      rw [hAt, hAt, hab]
    have h := congrArg (coeff SR) heq
    simpa only [coeff_synth] using h
  have hCs : Function.Surjective (C y) :=
    (LinearMap.injective_iff_surjective (f := (C y).toLinearMap)).mp hCi
  obtain ⟨aI, haI⟩ := hCs (Pi.basisFun ℝ (Fin 3) 0)
  obtain ⟨aJ, haJ⟩ := hCs (Pi.basisFun ℝ (Fin 3) 1)
  have hi (w : F) : SP.I (A y w) = A y (synth SR aI w) := by
    rw [hAt, haI, synth_basis]; rfl
  have hj (w : F) : SP.J (A y w) = A y (synth SR aJ w) := by
    rw [hAt, haJ, synth_basis]; rfl
  have hdef (a b : F) (c : Fin 3 → ℝ) :
      ∃ w, B a (synth SR c b) - synth SP (C y c) (B a b) = A y w := by
    let ur := U a
    let ΩR := inducedForm R.tangent DR q y ur
    let ΩP := inducedForm P.tangent DP p (G y) (fderiv ℝ G y ur)
    have hcommR (d : Fin 3 → ℝ) (w : F) :
        DR.form q y ur (synth SR d w) - synth SR d (DR.form q y ur w) =
          synth SR (ΩR d) w :=
      congrArg (fun L : F →L[ℝ] F => L w)
        (synth_inducedForm R.tangent DR q y ur hy.1 d).symm
    have hcommP (d : Fin 3 → ℝ) (w : E) :
        DP.form p (G y) (fderiv ℝ G y ur) (synth SP d w) -
          synth SP d (DP.form p (G y) (fderiv ℝ G y ur) w) = synth SP (ΩP d) w :=
      congrArg (fun L : E →L[ℝ] E => L w)
        (synth_inducedForm P.tangent DP p (G y) (fderiv ℝ G y ur) htarget d).symm
    obtain ⟨d, hd⟩ := hCs ((fderiv ℝ C y ur) c + ΩP (C y c) - C y (ΩR c))
    refine ⟨synth SR d b, ?_⟩
    change H ur (synth SR c b) - synth SP (C y c) (H ur b) = _
    rw [hessian_quaternionic_defect (synth SR) (synth SP) A C G y
      (DP.form p (G y)) (DR.form q y) hA hC hInter ΩR ΩP ur hcommR hcommP c b]
    rw [← hd, ← hAt]
  have hzero (a b : F) : B a b = 0 := by
    apply secondFundamental_zero SP (A y) B (synth SR aI) (synth SR aJ)
      hsym hnormal hi hj
    · intro d w
      simpa only [haI, synth_basis] using hdef d w aI
    · intro d w
      simpa only [haJ, synth_basis] using hdef d w aJ
  have h := hzero (S y u) v
  change H (U (S y u)) v = 0 at h
  rw [hUS] at h
  exact h

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionTotalGeodesy
