import QuaternionicSymmetry.ManifoldTwistorRawTransitionDerivative

/-!
# Covariance of the smooth local twistor complex operator

The actual manifold derivative of a raw twistor chart transition, including
the dependent tangent space of its sphere fiber, agrees with the quaternionic
connection transition used in the local almost-complex proof. Consequently
the smooth fixed-chart complex operators commute with the true transition
tangent maps on every chart overlap.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorHorizontalOverlap
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem rawSphereTransition_coefficient (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (a : coefficientSphere) :
    (rawSphereTransition Q p q (y,coefficientSphereHomeomorph a)).2 =
      coefficientSphereHomeomorph (rotatedCoefficient Q p q y hy a) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
    have h := (extChartAt 𝓘(ℝ,E) p).map_target hy.1
    simpa only [x, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using h
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
    simpa only [x, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hy.2
  change euclideanSphereCoordChange Q (achart E p) (achart E q) x
      (coefficientSphereHomeomorph a) =
    coefficientSphereHomeomorph
      (sphereTransition Q (achart E p) (achart E q) x _ _ a)
  dsimp [euclideanSphereCoordChange]
  rw [dif_pos ⟨hp,hq⟩]
  rfl

def rawTangentTransition (p q : M) (z : X (E := E)) : X (E := E) :=
  let r := rawSphereTransition Q p q (z.1.1,z.2.1)
  let w := mfderiv ((𝓘(ℝ,E)).prod (𝓡 2))
    ((𝓘(ℝ,E)).prod (𝓡 2)) (rawSphereTransition Q p q)
      (z.1.1,z.2.1) (z.1.2,z.2.2)
  ((r.1,w.1),⟨r.2,w.2⟩)

theorem rawTangentTransition_embedded_eq_local (D : CompatibleTangentConnection Q)
    (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (a : coefficientSphere) (u : E)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    let r := rawTangentTransition Q p q
      ((y,u),⟨coefficientSphereHomeomorph a,v⟩)
    (r.1.2,sphereTangentAmbient r.2) =
      ((localTangentTransition Q D p q y hy a
        (u,sphereTangentVerticalEquiv a v)).1,
       (localTangentTransition Q D p q y hy a
        (u,sphereTangentVerticalEquiv a v)).2.1) := by
  have hraw := rawSphereTransition_tangent_ambient Q p q y
    (coefficientSphereHomeomorph a) u v hy
  have hloc := localTangentTransition_eq_ambient Q D p q y hy a
    (u,sphereTangentVerticalEquiv a v)
  calc
    _ = ambientTransition Q p q y a.1
      (u,(sphereTangentVerticalEquiv a v).1) := by
        simpa only [rawTangentTransition,
          coefficientEmbedding, Homeomorph.symm_apply_apply,
          sphereTangentAmbient_eq_vertical] using hraw
    _ = _ := hloc.symm

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem sphereTangentAmbient_injective (s : geometricSphere) :
    Function.Injective
      (fun v : TangentSpace (𝓡 2) s =>
        sphereTangentAmbient
          (⟨s,v⟩ : TangentBundle (𝓡 2) geometricSphere)) := by
  intro v w h
  have h' := (EuclideanSpace.equiv (Fin 3) ℝ).injective h
  exact (mfderiv_coe_sphere_injective s) h'

theorem sphereTangentAmbient_total_injective :
    Function.Injective
      (fun t : TangentBundle (𝓡 2) geometricSphere =>
        (t.1,sphereTangentAmbient t)) := by
  rintro ⟨s,v⟩ ⟨s',v'⟩ h
  have hs : s = s' := congrArg Prod.fst h
  subst s'
  have hv : sphereTangentAmbient
      (⟨s,v⟩ : TangentBundle (𝓡 2) geometricSphere) =
      sphereTangentAmbient
        (⟨s,v'⟩ : TangentBundle (𝓡 2) geometricSphere) :=
    congrArg Prod.snd h
  congr
  exact sphereTangentAmbient_injective s hv

theorem ambientLocalComplex_transition (D : CompatibleTangentConnection Q)
    (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (a : coefficientSphere) (uv : E × verticalSubmodule a) :
    ambientTransition Q p q y a.1
      (ambientLocalComplex Q D p ((y,a.1),(uv.1,uv.2.1))) =
    ambientLocalComplex Q D q
      ((chartTransition (I := 𝓘(ℝ,E)) p q y,
        (rotatedCoefficient Q p q y hy a).1),
       ambientTransition Q p q y a.1 (uv.1,uv.2.1)) := by
  let T := localTangentTransition Q D p q y hy a
  have hp := ambientLocalComplex_eq_local Q D p y hy.1 a uv
  have hq := ambientLocalComplex_eq_local Q D q
    (chartTransition (I := 𝓘(ℝ,E)) p q y)
    ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
    (rotatedCoefficient Q p q y hy a) (T uv)
  have ht := localTangentTransition_eq_ambient Q D p q y hy a uv
  have htJ := localTangentTransition_eq_ambient Q D p q y hy a
    (localTwistorComplex Q D p y hy.1 a uv)
  have hc := localTangentTransition_complex Q D p q y hy a uv
  calc
    _ = ambientTransition Q p q y a.1
      ((localTwistorComplex Q D p y hy.1 a uv).1,
       (localTwistorComplex Q D p y hy.1 a uv).2.1) := by rw [hp]
    _ = ((T (localTwistorComplex Q D p y hy.1 a uv)).1,
         (T (localTwistorComplex Q D p y hy.1 a uv)).2.1) := htJ.symm
    _ = ((localTwistorComplex Q D q
        (chartTransition (I := 𝓘(ℝ,E)) p q y)
        ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
        (rotatedCoefficient Q p q y hy a) (T uv)).1,
       (localTwistorComplex Q D q
        (chartTransition (I := 𝓘(ℝ,E)) p q y)
        ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
        (rotatedCoefficient Q p q y hy a) (T uv)).2.1) := by rw [hc]
    _ = ambientLocalComplex Q D q
      ((chartTransition (I := 𝓘(ℝ,E)) p q y,
        (rotatedCoefficient Q p q y hy a).1),
       ((T uv).1,(T uv).2.1)) := hq.symm
    _ = _ := by rw [ht]

theorem rawTangentTransition_eq_local (D : CompatibleTangentConnection Q)
    (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (a : coefficientSphere) (u : E)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    let T := localTangentTransition Q D p q y hy a
      (u,sphereTangentVerticalEquiv a v)
    rawTangentTransition Q p q
      ((y,u),⟨coefficientSphereHomeomorph a,v⟩) =
    ((chartTransition (I := 𝓘(ℝ,E)) p q y,T.1),
      ⟨coefficientSphereHomeomorph (rotatedCoefficient Q p q y hy a),
        (sphereTangentVerticalEquiv (rotatedCoefficient Q p q y hy a)).symm T.2⟩) := by
  let r := rawTangentTransition Q p q
    ((y,u),⟨coefficientSphereHomeomorph a,v⟩)
  let T := localTangentTransition Q D p q y hy a
    (u,sphereTangentVerticalEquiv a v)
  have hEmb : (r.1.2,sphereTangentAmbient r.2) = (T.1,T.2.1) :=
    rawTangentTransition_embedded_eq_local Q D p q y hy a u v
  have hCoeff : r.2.1 =
      coefficientSphereHomeomorph (rotatedCoefficient Q p q y hy a) :=
    rawSphereTransition_coefficient Q p q y hy a
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact congrArg Prod.fst hEmb
  · apply sphereTangentAmbient_total_injective
    apply Prod.ext
    · exact hCoeff
    · change sphereTangentAmbient r.2 =
        sphereTangentAmbient
          (⟨coefficientSphereHomeomorph (rotatedCoefficient Q p q y hy a),
            (sphereTangentVerticalEquiv (rotatedCoefficient Q p q y hy a)).symm T.2⟩ :
            TangentBundle (𝓡 2) geometricSphere)
      rw [sphereTangentAmbient_eq_vertical]
      simpa using congrArg Prod.snd hEmb

theorem rawTangentTransition_complex (D : CompatibleTangentConnection Q)
    (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (a : coefficientSphere) (u : E)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    rawTangentTransition Q p q
      (localComplexTrivialized Q D p
        ((y,u),⟨coefficientSphereHomeomorph a,v⟩)) =
    localComplexTrivialized Q D q
      (rawTangentTransition Q p q
        ((y,u),⟨coefficientSphereHomeomorph a,v⟩)) := by
  let uv : E × verticalSubmodule a := (u,sphereTangentVerticalEquiv a v)
  let Jp := localTwistorComplex Q D p y hy.1 a uv
  let b := rotatedCoefficient Q p q y hy a
  let T := localTangentTransition Q D p q y hy a uv
  let yq := chartTransition (I := 𝓘(ℝ,E)) p q y
  have hq : yq ∈ (extChartAt 𝓘(ℝ,E) q).target :=
    (extChartAt 𝓘(ℝ,E) q).map_source hy.2
  have hJp : localComplexTrivialized Q D p
      ((y,u),⟨coefficientSphereHomeomorph a,v⟩) =
      ((y,Jp.1),⟨coefficientSphereHomeomorph a,
        (sphereTangentVerticalEquiv a).symm Jp.2⟩) := by
    simpa only [localComplexTrivialized, Jp, uv] using
      congrArg (fun w : Y (E := E) => ((y,w.1),w.2))
        (localComplexBundleMap_eq_local Q D p y hy.1 a u v)
  have hTJp := rawTangentTransition_eq_local Q D p q y hy a
    Jp.1 ((sphereTangentVerticalEquiv a).symm Jp.2)
  have hT := rawTangentTransition_eq_local Q D p q y hy a u v
  have hc := localTangentTransition_complex Q D p q y hy a uv
  calc
    _ = rawTangentTransition Q p q
      ((y,Jp.1),⟨coefficientSphereHomeomorph a,
        (sphereTangentVerticalEquiv a).symm Jp.2⟩) := by rw [hJp]
    _ = ((yq,(localTangentTransition Q D p q y hy a Jp).1),
        ⟨coefficientSphereHomeomorph b,
          (sphereTangentVerticalEquiv b).symm
            (localTangentTransition Q D p q y hy a Jp).2⟩) := by
          simpa only [LinearEquiv.apply_symm_apply, yq, b] using hTJp
    _ = ((yq,(localTwistorComplex Q D q yq hq b T).1),
        ⟨coefficientSphereHomeomorph b,
          (sphereTangentVerticalEquiv b).symm
            (localTwistorComplex Q D q yq hq b T).2⟩) := by rw [hc]
    _ = localComplexTrivialized Q D q
      ((yq,T.1),⟨coefficientSphereHomeomorph b,
        (sphereTangentVerticalEquiv b).symm T.2⟩) := by
          have h := localComplexBundleMap_eq_local Q D q yq hq b
            T.1 ((sphereTangentVerticalEquiv b).symm T.2)
          simpa only [localComplexTrivialized,
            LinearEquiv.apply_symm_apply] using
            (congrArg (fun w : Y (E := E) => ((yq,w.1),w.2)) h).symm
    _ = _ := by rw [hT]
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
