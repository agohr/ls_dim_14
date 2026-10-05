import QuaternionicSymmetry.ManifoldTwistorCoefficientEmbeddingDerivative

/-!
# Tangent derivative of the actual raw twistor sphere transition

The fixed raw-chart transition is smooth on each genuine overlap. After
embedding the sphere tangent in its ambient three-dimensional coefficient
space, its manifold derivative agrees with the Fréchet derivative of the
already verified ambient frame rotation. This identifies the geometric
sphere derivative required by the local almost-complex covariance theorem.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorHorizontalOverlap
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem rawSphereTransition_embedding (p q : M) (y : E)
    (s : geometricSphere) (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    productEmbedding (rawSphereTransition Q p q (y,s)) =
      ambientSphereTransition Q p q (productEmbedding (y,s)) := by
  apply Prod.ext
  · rfl
  · exact (ambientSphereTransition_sphereCore Q p q y s hy).symm

theorem rawSphereTransition_smoothAt (p q : M) (y : E)
    (s : geometricSphere) (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    ContMDiffAt ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2)) ∞
      (rawSphereTransition Q p q) (y,s) := by
  let z := fixedRawChartInv Q p (y,s)
  have hInv : ContMDiffAt ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2)) ∞
      (fixedRawChartInv Q p) (y,s) := by
    apply (fixedRawChartInv_smoothOn Q p).contMDiffAt
    have hopen : IsOpen (fixedRawTarget (E := E) p) :=
      (isOpen_extChartAt_target p).prod isOpen_univ
    exact hopen.mem_nhds ⟨hy.1,Set.mem_univ _⟩
  have hzq : z ∈ ((sphereCore Q).localTriv (achart E q)).toOpenPartialHomeomorph.source := by
    have hx : z.1 = (extChartAt 𝓘(ℝ,E) p).symm y := by
      exact (((sphereCore Q).localTriv (achart E p)).proj_symm_apply
        (by
          apply ((sphereCore Q).mem_localTriv_target (achart E p)
            ((extChartAt 𝓘(ℝ,E) p).symm y,s)).mpr
          rw [← (sphereCore Q).baseSet_at]
          have h := (extChartAt 𝓘(ℝ,E) p).map_target hy.1
          simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
            tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using h))
    apply ((sphereCore Q).mem_localTriv_source (achart E q) z).mpr
    rw [hx]
    rw [← (sphereCore Q).baseSet_at]
    have h := hy.2
    simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using h
  have hChart : ContMDiffAt ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2)) ∞ (fixedRawChart Q q) z :=
    (fixedRawChart_smoothOn Q q).contMDiffAt
      (((sphereCore Q).localTriv (achart E q)).toOpenPartialHomeomorph.open_source.mem_nhds hzq)
  have hcomp := hChart.comp (y,s) hInv
  have heq : (fun ys : E × geometricSphere =>
      fixedRawChart Q q (fixedRawChartInv Q p ys)) =ᶠ[𝓝 (y,s)]
      rawSphereTransition Q p q := by
    have hopen : IsOpen {ys : E × geometricSphere |
        ys.1 ∈ chartOverlap (I := 𝓘(ℝ,E)) p q} :=
      (chartOverlap_isOpen p q).preimage continuous_fst
    filter_upwards [hopen.mem_nhds hy] with ys hys
    exact fixedRawChart_transition Q p q ys.1 ys.2 hys
  exact hcomp.congr_of_eventuallyEq heq.symm

theorem ambientSphereTransition_mdifferentiableAt (p q : M) (y : E)
    (a : Fin 3 → ℝ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    MDifferentiableAt ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      (ambientSphereTransition Q p q) (y,a) := by
  have hphi : DifferentiableAt ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y :=
    (chartTransition_contDiffAt p q y hy).differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (rankThreeGauge Q p q) y :=
    (rankThreeGauge_contDiffAt Q p q y hy (by exact ENat.LEInfty.out)).differentiableAt
      (by norm_num)
  have hphiM : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (chartTransition (I := 𝓘(ℝ,E)) p q) y := hphi.mdifferentiableAt
  have hgM : MDifferentiableAt 𝓘(ℝ,E)
      𝓘(ℝ,(Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
      (rankThreeGauge Q p q) y := hg.mdifferentiableAt
  have hfirst : MDifferentiableAt
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ)) 𝓘(ℝ,E)
      (fun ya : E × (Fin 3 → ℝ) => chartTransition (I := 𝓘(ℝ,E)) p q ya.1) (y,a) :=
    hphiM.comp (f := Prod.fst) (y,a) mdifferentiableAt_fst
  have hga : MDifferentiableAt
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      𝓘(ℝ,(Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
      (fun ya : E × (Fin 3 → ℝ) => rankThreeGauge Q p q ya.1) (y,a) :=
    hgM.comp (f := Prod.fst) (y,a) mdifferentiableAt_fst
  have hsecond : MDifferentiableAt
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ)) 𝓘(ℝ,Fin 3 → ℝ)
      (fun ya : E × (Fin 3 → ℝ) => rankThreeGauge Q p q ya.1 ya.2) (y,a) :=
    hga.clm_apply mdifferentiableAt_snd
  exact hfirst.prodMk hsecond

theorem rawSphereTransition_mfderiv_embedded (p q : M) (y : E)
    (s : geometricSphere) (u : E) (v : TangentSpace (𝓡 2) s)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    let w := mfderiv ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2)) (rawSphereTransition Q p q) (y,s) (u,v)
    (w.1, sphereTangentAmbient
      (⟨(rawSphereTransition Q p q (y,s)).2,w.2⟩ :
        TangentBundle (𝓡 2) geometricSphere)) =
    mfderiv ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      (ambientSphereTransition Q p q)
      (productEmbedding (y,s))
      (u,sphereTangentAmbient (⟨s,v⟩ : TangentBundle (𝓡 2) geometricSphere)) := by
  let I := ((𝓘(ℝ,E)).prod (𝓡 2))
  let J := ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
  have hpe : ContMDiff I J ∞ (productEmbedding (E := E)) :=
    contMDiff_fst.prodMk
      (coefficientEmbedding_smooth.comp contMDiff_snd)
  have hraw : MDifferentiableAt I I (rawSphereTransition Q p q) (y,s) :=
    (rawSphereTransition_smoothAt Q p q y s hy).mdifferentiableAt (by simp)
  have hamb : MDifferentiableAt J J (ambientSphereTransition Q p q)
      (productEmbedding (y,s)) :=
    ambientSphereTransition_mdifferentiableAt Q p q y
      (coefficientEmbedding s) hy
  have heq : (productEmbedding (E := E) ∘ rawSphereTransition Q p q) =ᶠ[𝓝 (y,s)]
      (ambientSphereTransition Q p q ∘ productEmbedding) := by
    have hopen : IsOpen {ys : E × geometricSphere |
        ys.1 ∈ chartOverlap (I := 𝓘(ℝ,E)) p q} :=
      (chartOverlap_isOpen p q).preimage continuous_fst
    filter_upwards [hopen.mem_nhds hy] with ys hys
    exact rawSphereTransition_embedding Q p q ys.1 ys.2 hys
  have hder := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := J) heq
  rw [mfderiv_comp (y,s) (hpe.mdifferentiableAt (by simp)) hraw,
    mfderiv_comp (y,s) hamb (hpe.mdifferentiableAt (by simp))] at hder
  have happ := congrArg (fun L : (E × TangentSpace (𝓡 2) s) →L[ℝ]
      (E × (Fin 3 → ℝ)) => L (u,v)) hder
  change (mfderiv I J productEmbedding (rawSphereTransition Q p q (y,s)))
      ((mfderiv I I (rawSphereTransition Q p q) (y,s)) (u,v)) =
    (mfderiv J J (ambientSphereTransition Q p q) (productEmbedding (y,s)))
      ((mfderiv I J productEmbedding (y,s)) (u,v)) at happ
  rw [productEmbedding_mfderiv] at happ
  let r := rawSphereTransition Q p q (y,s)
  let w := (mfderiv I I (rawSphereTransition Q p q) (y,s)) (u,v)
  have hout : (mfderiv I J productEmbedding r) w =
      (w.1,sphereTangentAmbient
        (⟨r.2,w.2⟩ : TangentBundle (𝓡 2) geometricSphere)) := by
    simpa only [Prod.mk.eta] using
      (productEmbedding_mfderiv r.1 r.2 w.1 w.2)
  rw [hout] at happ
  exact happ

theorem ambientSphereTransition_mfderiv_eq_fderiv (p q : M)
    (y : E) (a : Fin 3 → ℝ)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    mfderiv ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      (ambientSphereTransition Q p q) (y,a) =
      fderiv ℝ (ambientSphereTransition Q p q) (y,a) := by
  simp only [mfderiv, mfld_simps]
  rw [if_pos (ambientSphereTransition_mdifferentiableAt Q p q y a hy)]
  simp

theorem rawSphereTransition_tangent_ambient (p q : M) (y : E)
    (s : geometricSphere) (u : E) (v : TangentSpace (𝓡 2) s)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    let w := mfderiv ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2)) (rawSphereTransition Q p q) (y,s) (u,v)
    (w.1, sphereTangentAmbient
      (⟨(rawSphereTransition Q p q (y,s)).2,w.2⟩ :
        TangentBundle (𝓡 2) geometricSphere)) =
    ambientTransition Q p q y (coefficientEmbedding s)
      (u,sphereTangentAmbient
        (⟨s,v⟩ : TangentBundle (𝓡 2) geometricSphere)) := by
  have h := rawSphereTransition_mfderiv_embedded Q p q y s u v hy
  simp only [productEmbedding] at h
  rw [ambientSphereTransition_mfderiv_eq_fderiv Q p q y (coefficientEmbedding s) hy] at h
  have hF := ambientSphereTransition_fderiv Q p q y (coefficientEmbedding s) hy
    (u,sphereTangentAmbient (⟨s,v⟩ : TangentBundle (𝓡 2) geometricSphere))
  exact h.trans hF

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
