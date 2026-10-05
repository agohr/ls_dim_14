import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficientChartDerivative
import QuaternionicSymmetry.ManifoldTwistorCenterRawDerivative
import QuaternionicSymmetry.ManifoldQuaternionicLocalSphereActionSmooth
import QuaternionicSymmetry.ManifoldTwistorCoefficientEmbeddingDerivative

/-! Relating the joint coefficient derivative to the genuine smooth
geometric-sphere derivative of an isometry's twistor lift. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometrySphereDerivative

open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex
open ManifoldQuaternionicIsometryCoefficientChartDerivative
open ManifoldQuaternionicIsometryInducedConnection
open ManifoldQuaternionicLocalSphereActionSmooth
open ManifoldQuaternionicSpanSymmetry
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

/-- The ordinary Euclidean coefficient vector of a geometric sphere point. -/
def sphereCoefficients (u : geometricSphere) : Fin 3 → ℝ :=
  EuclideanSpace.equiv (Fin 3) ℝ (u : EuclideanThree)

theorem sphereCoefficients_mfderiv (u : geometricSphere)
    (w : TangentSpace (𝓡 2) u) :
    mfderiv (𝓡 2) 𝓘(ℝ, Fin 3 → ℝ) sphereCoefficients u w =
      EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap u w) := by
  simpa only [sphereCoefficients,
      ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding,
      ManifoldTwistorGlobalAlmostComplex.sphereTangentAmbient,
      sphereTangentMap] using
    ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding_mfderiv u w

/-- The genuine product-manifold tangent in centered base coordinates and
ambient sphere coefficients. -/
def coefficientChart (p : M) (q : M × geometricSphere) : E × (Fin 3 → ℝ) :=
  (extChartAt 𝓘(ℝ,E) p q.1, sphereCoefficients q.2)

theorem coefficientChart_mfderiv_center (p : M) (u : geometricSphere)
    (v : E) (w : TangentSpace (𝓡 2) u) :
    mfderiv (J (E := E)) ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      (coefficientChart (E := E) p) (p,u) (v,w) =
      (v, EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap u w)) := by
  have hbs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) p) p := contMDiffAt_extChartAt
  have hb : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (extChartAt 𝓘(ℝ,E) p) p := hbs.mdifferentiableAt (by simp)
  have hs : MDifferentiableAt (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
      sphereCoefficients u := by
    change MDifferentiableAt (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
      ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding u
    exact ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding_smooth.mdifferentiableAt
      (by simp)
  change mfderiv (J (E := E)) ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
    (Prod.map (extChartAt 𝓘(ℝ,E) p) sphereCoefficients) (p,u) (v,w) = _
  rw [mfderiv_prodMap hb hs,
    ManifoldTwistorGlobalAlmostComplex.mfderiv_extChartAt_center]
  change (v, (mfderiv (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
    sphereCoefficients u) w) = _
  rw [sphereCoefficients_mfderiv]

/-- On the genuine fixed-chart overlap, the sphere lift is the restriction
of the jointly differentiable coefficient-linear field. -/
theorem localSphereAmbient_eq_coefficientField_on_overlap
    (f : QuaternionicIsometries Q) (p : M)
    (q : M × geometricSphere)
    (hx : q.1 ∈ (chartAt E p).source)
    (hy : f • q.1 ∈ (chartAt E (f • p)).source) :
    localSphereAmbient Q f p q =
      toEuclidean (coefficientLinearField Q f p
        (coefficientChart (E := E) p q).1
        (coefficientChart (E := E) p q).2) := by
  classical
  have hleft : (extChartAt 𝓘(ℝ,E) p).symm
      (extChartAt 𝓘(ℝ,E) p q.1) = q.1 :=
    (extChartAt 𝓘(ℝ,E) p).left_inv
      (by simpa only [extChartAt_source] using hx)
  rw [localSphereAmbient, if_pos ⟨hx,hy⟩]
  change toEuclidean (ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation
      Q f p q.1 (sphereCoefficients q.2)) =
    toEuclidean (coefficientOrbit Q f p (sphereCoefficients q.2)
      (extChartAt 𝓘(ℝ,E) p q.1))
  simp only [coefficientOrbit, hleft]

theorem localSphereAmbient_eq_coefficientField_eventually
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere) :
    localSphereAmbient Q f p =ᶠ[𝓝 (p,u)]
      fun q => toEuclidean (coefficientLinearField Q f p
        (coefficientChart (E := E) p q).1
        (coefficientChart (E := E) p q).2) := by
  have hf : Continuous (f.1 : M → M) := f.1.contMDiff.continuous
  have hopen : IsOpen {q : M × geometricSphere |
      q.1 ∈ (chartAt E p).source ∧
        f • q.1 ∈ (chartAt E (f • p)).source} := by
    exact ((chartAt E p).open_source.inter
      ((chartAt E (f • p)).open_source.preimage hf)).preimage continuous_fst
  filter_upwards [hopen.mem_nhds
      (⟨mem_chart_source E p, mem_chart_source E (f • p)⟩ :
        (p,u) ∈ {q : M × geometricSphere |
          q.1 ∈ (chartAt E p).source ∧
            f • q.1 ∈ (chartAt E (f • p)).source})] with q hq
  exact localSphereAmbient_eq_coefficientField_on_overlap Q f p q hq.1 hq.2

/-- Ambient coefficients of the genuine sphere action, avoiding any
chart-level identification of sphere tangent vectors. -/
def localSphereCoefficients (f : QuaternionicIsometries Q) (p : M)
    (q : M × geometricSphere) : Fin 3 → ℝ :=
  sphereCoefficients (localSphereAction Q f p q)

theorem localSphereCoefficients_eq_coefficientField_eventually
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere) :
    localSphereCoefficients Q f p =ᶠ[𝓝 (p,u)]
      fun q => coefficientLinearField Q f p
        (coefficientChart (E := E) p q).1
        (coefficientChart (E := E) p q).2 := by
  filter_upwards [localSphereAmbient_eq_coefficientField_eventually Q f p u]
    with q hq
  change (EuclideanSpace.equiv (Fin 3) ℝ)
    (localSphereAmbient Q f p q) = _
  rw [hq]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply _

theorem coefficientChart_mdifferentiableAt_center (p : M)
    (u : geometricSphere) :
    MDifferentiableAt (J (E := E))
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      (coefficientChart (E := E) p) (p,u) := by
  have hb : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (extChartAt 𝓘(ℝ,E) p) p := by
    have h : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
        (extChartAt 𝓘(ℝ,E) p) p := contMDiffAt_extChartAt
    exact h.mdifferentiableAt (by simp)
  have hs : MDifferentiableAt (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
      sphereCoefficients u := by
    change MDifferentiableAt (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
      ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding u
    exact ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding_smooth.mdifferentiableAt
      (by simp)
  change MDifferentiableAt (J (E := E))
    ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
    (Prod.map (extChartAt 𝓘(ℝ,E) p) sphereCoefficients) (p,u)
  exact hb.prodMap hs

theorem localSphereCoefficients_mfderiv_center
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere)
    (v : E) (w : TangentSpace (𝓡 2) u) :
    mfderiv (J (E := E)) 𝓘(ℝ,Fin 3 → ℝ)
      (localSphereCoefficients Q f p) (p,u) (v,w) =
      fderiv ℝ (coefficientOrbit Q f p (sphereCoefficients u))
        (extChartAt 𝓘(ℝ,E) p p) v +
      coefficientOrbit Q f p
        (EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap u w))
        (extChartAt 𝓘(ℝ,E) p p) := by
  let P : E × (Fin 3 → ℝ) → Fin 3 → ℝ :=
    fun q => coefficientLinearField Q f p q.1 q.2
  have hP : DifferentiableAt ℝ P
      (extChartAt 𝓘(ℝ,E) p p, sphereCoefficients u) := by
    have hfield := coefficientLinearField_differentiableAt_center Q f p
    dsimp only [P]
    fun_prop
  have hPmd : MDifferentiableAt
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ)) 𝓘(ℝ,Fin 3 → ℝ)
      P (extChartAt 𝓘(ℝ,E) p p, sphereCoefficients u) := by
    simpa only [modelWithCornersSelf_prod, chartedSpaceSelf_prod] using
      hP.mdifferentiableAt
  have hK := coefficientChart_mdifferentiableAt_center (E := E) p u
  have hcomp := mfderiv_comp (p,u) hPmd hK
  have hevent := localSphereCoefficients_eq_coefficientField_eventually Q f p u
  rw [hevent.mfderiv_eq (I := J (E := E))
    (I' := 𝓘(ℝ,Fin 3 → ℝ))]
  change mfderiv (J (E := E)) 𝓘(ℝ,Fin 3 → ℝ)
    (P ∘ coefficientChart (E := E) p) (p,u) (v,w) = _
  rw [hcomp]
  change (mfderiv ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      𝓘(ℝ,Fin 3 → ℝ) P
      (extChartAt 𝓘(ℝ,E) p p, sphereCoefficients u))
    ((mfderiv (J (E := E)) ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      (coefficientChart (E := E) p) (p,u)) (v,w)) = _
  rw [coefficientChart_mfderiv_center,
    mfderiv_prod_eq_add_apply hPmd]
  simp only [mfderiv_eq_fderiv]
  change fderiv ℝ (coefficientOrbit Q f p (sphereCoefficients u))
      (extChartAt 𝓘(ℝ,E) p p) v +
    fderiv ℝ (coefficientLinearField Q f p
      (extChartAt 𝓘(ℝ,E) p p)) (sphereCoefficients u)
      (EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap u w)) = _
  rw [ContinuousLinearMap.fderiv]
  rfl

/-- The actual sphere-tangent differential, expressed by its injective
Euclidean coefficient embedding. This includes both the base and vertical
variations, so it is stronger than fiberwise derivative equivariance. -/
theorem localSphereAction_mfderiv_coefficients_center
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere)
    (v : E) (w : TangentSpace (𝓡 2) u) :
    EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (localSphereAction Q f p (p,u))
        (mfderiv (J (E := E)) (𝓡 2)
          (localSphereAction Q f p) (p,u) (v,w))) =
      fderiv ℝ (coefficientOrbit Q f p (sphereCoefficients u))
        (extChartAt 𝓘(ℝ,E) p p) v +
      coefficientOrbit Q f p
        (EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap u w))
        (extChartAt 𝓘(ℝ,E) p p) := by
  have hS : MDifferentiableAt (J (E := E)) (𝓡 2)
      (localSphereAction Q f p) (p,u) :=
    (localSphereAction_smoothAt_center Q f p u).mdifferentiableAt (by simp)
  have hC : MDifferentiableAt (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
      sphereCoefficients (localSphereAction Q f p (p,u)) := by
    change MDifferentiableAt (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
      ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding
        (localSphereAction Q f p (p,u))
    exact ManifoldTwistorGlobalAlmostComplex.coefficientEmbedding_smooth.mdifferentiableAt
      (by simp)
  have hcomp := mfderiv_comp (p,u) hC hS
  have hvalue := congrArg (fun L : (E × TangentSpace (𝓡 2) u) →L[ℝ]
      (Fin 3 → ℝ) => L (v,w)) hcomp
  change mfderiv (J (E := E)) 𝓘(ℝ,Fin 3 → ℝ)
      (localSphereCoefficients Q f p) (p,u) (v,w) = _ at hvalue
  change mfderiv (J (E := E)) 𝓘(ℝ,Fin 3 → ℝ)
      (localSphereCoefficients Q f p) (p,u) (v,w) =
    (mfderiv (𝓡 2) 𝓘(ℝ,Fin 3 → ℝ)
      sphereCoefficients (localSphereAction Q f p (p,u)))
        ((mfderiv (J (E := E)) (𝓡 2)
          (localSphereAction Q f p) (p,u)) (v,w)) at hvalue
  rw [sphereCoefficients_mfderiv] at hvalue
  exact hvalue.symm.trans (localSphereCoefficients_mfderiv_center Q f p u v w)

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometrySphereDerivative
