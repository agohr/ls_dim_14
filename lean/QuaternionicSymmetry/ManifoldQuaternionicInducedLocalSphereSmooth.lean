import QuaternionicSymmetry.ManifoldQuaternionicInducedLocalCoefficientJointSmooth
import QuaternionicSymmetry.ManifoldQuaternionicSphereSmoothAt

/-! A smooth geometric-sphere map in fixed source and target adapted charts,
induced by a genuine quaternionic submanifold embedding. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedLocalSphereSmooth
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicInducedLocalCoefficientJointSmooth
open ManifoldQuaternionicSphereSmoothAt
open ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere
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

private abbrev J := 𝓘(ℝ,F).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩


def localSphereAmbient (c : N) (q : N × geometricSphere) : EuclideanThree := by
  classical
  exact if q.1 ∈ (chartAt F c).source ∧
      ι q.1 ∈ (chartAt E (ι c)).source then
    toEuclidean (localCoefficientMap P R ι hι hR
      (achart F c) (achart E (ι c)) q.1
      (EuclideanSpace.equiv (Fin 3) ℝ q.2.1))
  else q.2.1

theorem localSphereAmbient_mem_sphere (c : N) (q : N × geometricSphere) :
    localSphereAmbient P R ι hι hR c q ∈
      Metric.sphere (0 : EuclideanThree) 1 := by
  classical
  by_cases hq : q.1 ∈ (chartAt F c).source ∧
      ι q.1 ∈ (chartAt E (ι c)).source
  · rw [localSphereAmbient, if_pos hq]
    apply (mem_geometricSphere _).2
    rw [localCoefficientMap_squareNorm P R ι hι hR
      (achart F c) (achart E (ι c)) q.1 hq.1 hq.2]
    exact (mem_geometricSphere _).1 (by
      simpa [toEuclidean] using q.2.2)
  · simpa only [localSphereAmbient, if_neg hq] using q.2.2

def localSphereMap (c : N) : N × geometricSphere → geometricSphere :=
  Set.codRestrict (localSphereAmbient P R ι hι hR c)
    (Metric.sphere (0 : EuclideanThree) 1)
    (localSphereAmbient_mem_sphere P R ι hι hR c)

include hSmooth in
theorem localSphereAmbient_smoothAt_center (c : N) (u : geometricSphere) :
    ContMDiffAt (J (F := F)) 𝓘(ℝ,EuclideanThree) ∞
      (localSphereAmbient P R ι hι hR c) (c,u) := by
  classical
  let T := 𝓘(ℝ,F).prod 𝓘(ℝ,Fin 3 → ℝ)
  have hfst : ContMDiffAt (J (F := F)) 𝓘(ℝ,F) ∞
      (Prod.fst : N × geometricSphere → N) (c,u) := contMDiffAt_fst
  have hsnd : ContMDiffAt (J (F := F)) (𝓡 2) ∞
      (Prod.snd : N × geometricSphere → geometricSphere) (c,u) :=
    contMDiffAt_snd
  have hcoe : ContMDiffAt (J (F := F)) 𝓘(ℝ,EuclideanThree) ∞
      (fun q : N × geometricSphere => (q.2 : EuclideanThree)) (c,u) :=
    (contMDiff_coe_sphere (n := 2) (E := EuclideanThree)).contMDiffAt.comp
      (c,u) hsnd
  have hcoeff : ContMDiffAt (J (F := F)) 𝓘(ℝ,Fin 3 → ℝ) ∞
      (fun q : N × geometricSphere =>
        EuclideanSpace.equiv (Fin 3) ℝ (q.2 : EuclideanThree)) (c,u) :=
    ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).contMDiffAt.comp
      (c,u) hcoe
  have hpair : ContMDiffAt (J (F := F)) T ∞
      (fun q : N × geometricSphere =>
        (q.1, EuclideanSpace.equiv (Fin 3) ℝ (q.2 : EuclideanThree)))
      (c,u) := hfst.prodMk hcoeff
  have hrot := (localCoefficientMap_jointSmoothAt_center P R ι
    hSmooth hι hR c (EuclideanSpace.equiv (Fin 3) ℝ (u : EuclideanThree))).comp
      (c,u) hpair
  have hambient : ContMDiffAt (J (F := F)) 𝓘(ℝ,EuclideanThree) ∞
      (fun q : N × geometricSphere =>
        toEuclidean (localCoefficientMap P R ι hι hR
          (achart F c) (achart E (ι c)) q.1
          (EuclideanSpace.equiv (Fin 3) ℝ q.2.1))) (c,u) :=
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff).contMDiffAt.comp
      (c,u) hrot
  have hopen : IsOpen {q : N × geometricSphere |
      q.1 ∈ (chartAt F c).source ∧
        ι q.1 ∈ (chartAt E (ι c)).source} :=
    ((chartAt F c).open_source.inter
      ((chartAt E (ι c)).open_source.preimage hSmooth.continuous)).preimage
      continuous_fst
  have hmem : (c,u) ∈ {q : N × geometricSphere |
      q.1 ∈ (chartAt F c).source ∧
        ι q.1 ∈ (chartAt E (ι c)).source} :=
    ⟨mem_chart_source F c, mem_chart_source E (ι c)⟩
  apply hambient.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hmem] with q hq
  simp only [localSphereAmbient, if_pos hq]

include hSmooth in
theorem localSphereMap_smoothAt_center (c : N) (u : geometricSphere) :
    ContMDiffAt (J (F := F)) (𝓡 2) ∞
      (localSphereMap P R ι hι hR c) (c,u) :=
  contMDiffAt_codRestrict_sphere
    (localSphereAmbient_smoothAt_center P R ι hSmooth hι hR c u)
    (localSphereAmbient_mem_sphere P R ι hι hR c)

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedLocalSphereSmooth
