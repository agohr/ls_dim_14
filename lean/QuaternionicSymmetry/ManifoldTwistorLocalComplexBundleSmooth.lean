import QuaternionicSymmetry.ManifoldTwistorSmoothVerticalComplex

/-!
# Smooth fixed-chart twistor tangent operator

For a fixed base chart, the connection-corrected almost-complex formula is a
smooth map from raw base coordinates, base tangent directions and the actual
sphere tangent bundle to the corresponding product tangent bundle. The radial
inverse realizes its vertical component as a genuine sphere tangent vector.
The fiberwise formula is the previously checked local twistor operator.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorRadialRetraction
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
abbrev V := Fin 3 → ℝ
abbrev X := (E × E) × TangentBundle (𝓡 2) geometricSphere
abbrev IX := ((𝓘(ℝ,E)).prod 𝓘(ℝ,E)).prod (𝓡 2).tangent
abbrev Y := E × TangentBundle (𝓡 2) geometricSphere
abbrev IY := (𝓘(ℝ,E)).prod (𝓡 2).tangent

def localComplexBundleMap (p : M) (z : X (E := E)) : Y (E := E) :=
  let c := ambientLocalComplex Q D p
    ((z.1.1, (coefficientSphereHomeomorph.symm z.2.1).1),
      (z.1.2, sphereTangentAmbient z.2))
  (c.1, radialTangentMap
    (z.2.1, (EuclideanSpace.equiv (Fin 3) ℝ).symm c.2))

def localDomain (p : M) : Set (X (E := E)) :=
  {z | z.1.1 ∈ (extChartAt 𝓘(ℝ,E) p).target}

theorem localComplexBundleMap_smooth (p : M) :
    ContMDiffOn (IX (E := E)) (IY (E := E)) ∞
      (localComplexBundleMap Q D p) (localDomain (E := E) p) := by
  let s := localDomain (E := E) p
  have hfirst : ContMDiff (IX (E := E)) 𝓘(ℝ,E) ∞
      (fun z : X (E := E) => z.1.1) :=
    contMDiff_fst.comp contMDiff_fst
  have hu : ContMDiff (IX (E := E)) 𝓘(ℝ,E) ∞
      (fun z : X (E := E) => z.1.2) :=
    contMDiff_snd.comp contMDiff_fst
  have ht : ContMDiff (IX (E := E)) (𝓡 2).tangent ∞
      (fun z : X (E := E) => z.2) := contMDiff_snd
  have ha : ContMDiff (IX (E := E)) (𝓡 2) ∞
      (fun z : X (E := E) => z.2.1) :=
    (Bundle.contMDiff_proj (TangentSpace (𝓡 2))).comp ht
  have hcoef0 : ContMDiff (𝓡 2) 𝓘(ℝ,V) ∞
      (fun a : geometricSphere => (coefficientSphereHomeomorph.symm a).1) := by
    convert ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).comp
      (contMDiff_coe_sphere (n := 2) (E := EuclideanThree)) using 1
  have hcoef : ContMDiff (IX (E := E)) 𝓘(ℝ,V) ∞
      (fun z : X (E := E) => (coefficientSphereHomeomorph.symm z.2.1).1) :=
    hcoef0.comp ha
  have hv : ContMDiff (IX (E := E)) 𝓘(ℝ,V) ∞
      (fun z : X (E := E) => sphereTangentAmbient z.2) :=
    sphereTangentAmbient_smooth.comp ht
  have hin : ContMDiff (IX (E := E))
      𝓘(ℝ,(E × V) × (E × V)) ∞
      (fun z : X (E := E) =>
        ((z.1.1,(coefficientSphereHomeomorph.symm z.2.1).1),
          (z.1.2,sphereTangentAmbient z.2))) :=
    (hfirst.prodMk_space hcoef).prodMk_space (hu.prodMk_space hv)
  have hmap : Set.MapsTo
      (fun z : X (E := E) =>
        ((z.1.1,(coefficientSphereHomeomorph.symm z.2.1).1),
          (z.1.2,sphereTangentAmbient z.2)))
      s (((extChartAt 𝓘(ℝ,E) p).target ×ˢ Set.univ) ×ˢ Set.univ) := by
    intro z hz
    exact ⟨⟨hz, Set.mem_univ _⟩, Set.mem_univ _⟩
  have hc : ContMDiffOn (IX (E := E)) 𝓘(ℝ,E × V) ∞
      (fun z : X (E := E) => ambientLocalComplex Q D p
        ((z.1.1,(coefficientSphereHomeomorph.symm z.2.1).1),
          (z.1.2,sphereTangentAmbient z.2))) s :=
    (ambientLocalComplex_smooth Q D p).contMDiffOn.comp hin.contMDiffOn hmap
  have hbase : ContMDiffOn (IX (E := E)) 𝓘(ℝ,E) ∞
      (fun z : X (E := E) => (ambientLocalComplex Q D p
        ((z.1.1,(coefficientSphereHomeomorph.symm z.2.1).1),
          (z.1.2,sphereTangentAmbient z.2))).1) s :=
    (ContinuousLinearMap.fst ℝ E V).contMDiff.comp_contMDiffOn hc
  have hvertical : ContMDiffOn (IX (E := E)) 𝓘(ℝ,V) ∞
      (fun z : X (E := E) => (ambientLocalComplex Q D p
        ((z.1.1,(coefficientSphereHomeomorph.symm z.2.1).1),
          (z.1.2,sphereTangentAmbient z.2))).2) s :=
    (ContinuousLinearMap.snd ℝ E V).contMDiff.comp_contMDiffOn hc
  have hradial : ContMDiffOn (IX (E := E)) (𝓡 2).tangent ∞
      (fun z : X (E := E) => radialTangentMap
        (z.2.1, (EuclideanSpace.equiv (Fin 3) ℝ).symm
          (ambientLocalComplex Q D p
            ((z.1.1,(coefficientSphereHomeomorph.symm z.2.1).1),
              (z.1.2,sphereTangentAmbient z.2))).2)) s := by
    exact radialTangentMap_smooth.comp_contMDiffOn
      (ha.contMDiffOn.prodMk
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hvertical))
  exact hbase.prodMk hradial

theorem localComplexBundleMap_eq_local (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere)
    (u : E) (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    localComplexBundleMap Q D p
      ((y,u), ⟨coefficientSphereHomeomorph a,v⟩) =
    ((localTwistorComplex Q D p y hy a
      (u,sphereTangentVerticalEquiv a v)).1,
      ⟨coefficientSphereHomeomorph a,
        (sphereTangentVerticalEquiv a).symm
          (localTwistorComplex Q D p y hy a
            (u,sphereTangentVerticalEquiv a v)).2⟩) := by
  apply Prod.ext
  · simp only [localComplexBundleMap, Homeomorph.symm_apply_apply,
      sphereTangentAmbient_eq_vertical]
    exact congrArg Prod.fst
      (ambientLocalComplex_eq_local Q D p y hy a
        (u,sphereTangentVerticalEquiv a v))
  · apply Bundle.TotalSpace.ext
    · rfl
    · apply heq_of_eq
      simp only [localComplexBundleMap, radialTangentMap,
        Homeomorph.symm_apply_apply, sphereTangentAmbient_eq_vertical]
      rw [congrArg Prod.snd
        (ambientLocalComplex_eq_local Q D p y hy a
          (u,sphereTangentVerticalEquiv a v))]
      exact radialDerivative_eq_verticalInverse a
        (localTwistorComplex Q D p y hy a
          (u,sphereTangentVerticalEquiv a v)).2

theorem localComplexBundleMap_sq (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere)
    (u : E) (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    let w := localComplexBundleMap Q D p
      ((y,u), ⟨coefficientSphereHomeomorph a,v⟩)
    localComplexBundleMap Q D p ((y,w.1),w.2) =
      (-u, ⟨coefficientSphereHomeomorph a,-v⟩) := by
  simp only
  rw [localComplexBundleMap_eq_local Q D p y hy a u v]
  rw [localComplexBundleMap_eq_local Q D p y hy a]
  simp only [LinearEquiv.apply_symm_apply]
  rw [localTwistorComplex_sq]
  simp

/-- The local complex operator as a smooth map on a fixed product tangent
trivialization, retaining the base coordinate. -/
def localComplexTrivialized (p : M) (z : X (E := E)) : X (E := E) :=
  ((z.1.1, (localComplexBundleMap Q D p z).1),
    (localComplexBundleMap Q D p z).2)

theorem localComplexTrivialized_smooth (p : M) :
    ContMDiffOn (IX (E := E)) (IX (E := E)) ∞
      (localComplexTrivialized Q D p) (localDomain (E := E) p) := by
  have hmap := localComplexBundleMap_smooth Q D p
  have hbase : ContMDiffOn (IX (E := E)) 𝓘(ℝ,E) ∞
      (fun z : X (E := E) => z.1.1) (localDomain (E := E) p) :=
    (contMDiff_fst.comp contMDiff_fst).contMDiffOn
  have hdir : ContMDiffOn (IX (E := E)) 𝓘(ℝ,E) ∞
      (fun z : X (E := E) => (localComplexBundleMap Q D p z).1)
        (localDomain (E := E) p) :=
    contMDiff_fst.comp_contMDiffOn hmap
  have hvert : ContMDiffOn (IX (E := E)) (𝓡 2).tangent ∞
      (fun z : X (E := E) => (localComplexBundleMap Q D p z).2)
        (localDomain (E := E) p) :=
    contMDiff_snd.comp_contMDiffOn hmap
  exact (hbase.prodMk hdir).prodMk hvert

omit [Nontrivial E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem isOpen_localDomain (p : M) : IsOpen (localDomain (E := E) p) := by
  exact (isOpen_extChartAt_target p).preimage
    (continuous_fst.comp continuous_fst)

theorem localComplexTrivialized_smoothAt (p : M) (z : X (E := E))
    (hz : z ∈ localDomain (E := E) p) :
    ContMDiffAt (IX (E := E)) (IX (E := E)) ∞
      (localComplexTrivialized Q D p) z :=
  (localComplexTrivialized_smooth Q D p).contMDiffAt
    ((isOpen_localDomain (E := E) p).mem_nhds hz)

theorem localComplexTrivialized_sq (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere)
    (u : E) (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    localComplexTrivialized Q D p
      (localComplexTrivialized Q D p
        ((y,u),⟨coefficientSphereHomeomorph a,v⟩)) =
      ((y,-u),⟨coefficientSphereHomeomorph a,-v⟩) := by
  simp only [localComplexTrivialized]
  exact congrArg (fun w : Y (E := E) => ((y,w.1),w.2))
    (localComplexBundleMap_sq Q D p y hy a u v)

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
