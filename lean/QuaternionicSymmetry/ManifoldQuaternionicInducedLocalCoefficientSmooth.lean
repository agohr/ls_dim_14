import QuaternionicSymmetry.ManifoldQuaternionicInducedLocalDerivativeSmooth
import QuaternionicSymmetry.ManifoldQuaternionicLocalSynthSmooth

/-! The induced rank-three coefficient map is smooth after transport to
fixed adapted source and target charts. Preferred `indexAt` gauges need not
be smooth, so the conclusion is intentionally local-chart based. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedLocalCoefficientSmooth
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicInducedLocalDerivativeSmooth
open ManifoldQuaternionicLocalSynthSmooth
open ManifoldQuaternionicLocalGaugeTransport
open ManifoldQuaternionicMetric
open scoped Manifold ContDiff Topology
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

include hSmooth in
/-- Every matrix entry of the genuine induced coefficient map is smooth in
fixed adapted charts around a chosen source point. -/
theorem localCoefficientMap_entry_smoothAt_center
    (c : N) (a : Fin 3 → ℝ) (k : Fin 3) :
    ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞
      (fun x => (localCoefficientMap P R ι hι hR
        (achart F c) (achart E (ι c)) x a) k) c := by
  let i := achart F c
  let j := achart E (ι c)
  let D : N → F →L[ℝ] E := fun x => localDerivative ι i j x
  obtain ⟨w, hw⟩ := exists_ne (0 : F)
  have hi : c ∈ R.tangent.frames.adaptedCore.baseSet i :=
    R.tangent.frames.adaptedCore.mem_baseSet_at c
  have hj : ι c ∈ P.tangent.frames.adaptedCore.baseSet j :=
    P.tangent.frames.adaptedCore.mem_baseSet_at (ι c)
  have hs : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞
      (fun x => localTangentSynth R.tangent i x a) c :=
    ((smooth_localTangentSynth R.tangent i a) c hi).contMDiffAt
      ((R.tangent.frames.adaptedCore.isOpen_baseSet i).mem_nhds hi)
  have hDs : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞
      (fun x => D x (localTangentSynth R.tangent i x a w)) c :=
    (localDerivative_smoothAt_center ι hSmooth c).clm_apply
      (hs.clm_apply contMDiffAt_const)
  have hDw : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞
      (fun x => D x w) c :=
    (localDerivative_smoothAt_center ι hSmooth c).clm_apply contMDiffAt_const
  have hSk : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun x => localTangentSynth P.tangent j (ι x)
        (Pi.basisFun ℝ (Fin 3) k)) c :=
    (((smooth_localTangentSynth P.tangent j
      (Pi.basisFun ℝ (Fin 3) k)) (ι c) hj).contMDiffAt
      ((P.tangent.frames.adaptedCore.isOpen_baseSet j).mem_nhds hj)).comp c
      hSmooth.contMDiffAt
  have hSkDw : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞
      (fun x => localTangentSynth P.tangent j (ι x)
        (Pi.basisFun ℝ (Fin 3) k) (D x w)) c :=
    hSk.clm_apply hDw
  have hMetric : ContMDiffAt 𝓘(ℝ,F)
      𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => P.tangent.chartMetricForm j (ι x)) c :=
    (((P.tangent.smooth_chartMetricForm j) (ι c) hj).contMDiffAt
      ((P.tangent.frames.adaptedCore.isOpen_baseSet j).mem_nhds hj)).comp c
      hSmooth.contMDiffAt
  let numerator : N → ℝ := fun x => P.tangent.chartMetricForm j (ι x)
    (D x (localTangentSynth R.tangent i x a w))
    (localTangentSynth P.tangent j (ι x)
      (Pi.basisFun ℝ (Fin 3) k) (D x w))
  let denominator : N → ℝ := fun x => P.tangent.chartMetricForm j (ι x)
    (D x w) (D x w)
  have hNum : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞ numerator c :=
    (hMetric.clm_apply hDs).clm_apply hSkDw
  have hDen : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞ denominator c :=
    (hMetric.clm_apply hDw).clm_apply hDw
  have hDenNe : denominator c ≠ 0 :=
    ne_of_gt (localDerivative_chartMetric_pos P R ι hι i j c hi hj w hw)
  have hQuot : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞
      (fun x => numerator x / denominator x) c := by
    have hOuter : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => p.1 / p.2)
        (numerator c, denominator c) :=
      contDiffAt_fst.div contDiffAt_snd hDenNe
    exact ContDiffAt.comp_contMDiffAt
      (f := fun x : N => (numerator x, denominator x))
      hOuter (hNum.prodMk_space hDen)
  have hsource : ∀ᶠ x in 𝓝 c,
      x ∈ R.tangent.frames.adaptedCore.baseSet i :=
    (R.tangent.frames.adaptedCore.isOpen_baseSet i).mem_nhds hi
  have htarget : ∀ᶠ x in 𝓝 c,
      ι x ∈ P.tangent.frames.adaptedCore.baseSet j :=
    ((P.tangent.frames.adaptedCore.isOpen_baseSet j).preimage
      hSmooth.continuous).mem_nhds hj
  apply hQuot.congr_of_eventuallyEq
  filter_upwards [hsource, htarget] with x hx hy
  exact localCoefficientMap_eq_metric_div P R ι hι hR i j x hx hy a w hw k

include hSmooth in
/-- Smoothness of the entire fixed-chart coefficient vector for one fixed
source coefficient. This is the useful fiberwise input for the product-chart
sphere-bundle map. -/
theorem localCoefficientMap_apply_smoothAt_center
    (c : N) (a : Fin 3 → ℝ) :
    ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,Fin 3 → ℝ) ∞
      (fun x => localCoefficientMap P R ι hι hR
        (achart F c) (achart E (ι c)) x a) c := by
  apply contMDiffAt_pi_space.mpr
  intro k
  exact localCoefficientMap_entry_smoothAt_center P R ι hSmooth hι hR c a k

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedLocalCoefficientSmooth
