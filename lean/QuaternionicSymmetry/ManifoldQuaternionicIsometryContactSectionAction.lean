import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactSections
import QuaternionicSymmetry.ManifoldQuaternionicTwistorLiftSmooth

/-! The contact-section equivalences of actual quaternionic isometries
obey the group laws. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryContactSectionAction

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicHolomorphicContactFiberAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactSections
open ManifoldQuaternionicTwistorLiftSmooth
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

local instance : Fact (Module.finrank ℝ
    ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

theorem contactLineFiberMap_one
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B)
    (z : SphereBundleTotal Q) (v : L.core.Fiber z) :
    cast (congrArg L.core.Fiber (one_smul
      (QuaternionicIsometries Q) z))
      (contactLineFiberMap Q D L 1 z v) = v := by
  obtain ⟨w, rfl⟩ := contactFormReal_surjective Q D L z v
  have h := contactLineFiberMap_contactFormReal Q D L 1 z w
  have hbase : sphereTotalMap Q (1 : QuaternionicIsometries Q) = id := by
    funext x
    exact one_smul (QuaternionicIsometries Q) x
  rw [hbase] at h
  simpa only [mfderiv_id, ContinuousLinearMap.id_apply] using h

theorem contactSectionEquiv_one
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) :
    letI := B.charts
    contactSectionEquiv Q D B C 1 = LinearEquiv.refl ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line)) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  apply LinearEquiv.ext
  intro s
  apply ContMDiffSection.ext
  intro z
  have h := contactSectionEquiv_apply_at_image Q D B C 1 s z
  have h1 := contactLineFiberMap_one Q D C.line z (s z)
  have hbase : sphereTotalMap Q (1 : QuaternionicIsometries Q) z = z :=
    one_smul (QuaternionicIsometries Q) z
  rw [hbase] at h
  simp only [cast_eq] at h1
  have hfiber : contactLineFiberEquiv Q D C.line 1 z (s z) = s z := by
    simpa only [contactLineFiberEquiv_apply] using h1
  simpa only [LinearEquiv.refl_apply] using h.trans hfiber

theorem sphereTotalMap_tangentMap_mul
    (f g : QuaternionicIsometries Q) :
    tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q (f * g)) =
      tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q f) ∘
        tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q g) := by
  have hfun : sphereTotalMap Q (f * g) =
      sphereTotalMap Q f ∘ sphereTotalMap Q g := by
    funext x
    exact mul_smul f g x
  rw [hfun]
  exact tangentMap_comp
    ((sphereTotalMap_contMDiff Q f).mdifferentiable (by simp))
    ((sphereTotalMap_contMDiff Q g).mdifferentiable (by simp))

theorem sphereTotalMap_mfderiv_mul
    (f g : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) (v : TangentSpace (J (E := E)) z) :
    HEq (mfderiv (J (E := E)) (J (E := E))
      (sphereTotalMap Q (f * g)) z v)
      (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f)
        (sphereTotalMap Q g z)
        (mfderiv (J (E := E)) (J (E := E))
          (sphereTotalMap Q g) z v)) := by
  have h := congrFun (sphereTotalMap_tangentMap_mul Q f g)
    (⟨z, v⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q))
  change (⟨sphereTotalMap Q (f * g) z,
      mfderiv (J (E := E)) (J (E := E))
        (sphereTotalMap Q (f * g)) z v⟩ :
        TangentBundle (J (E := E)) (SphereBundleTotal Q)) =
    ⟨sphereTotalMap Q f (sphereTotalMap Q g z),
      mfderiv (J (E := E)) (J (E := E))
        (sphereTotalMap Q f) (sphereTotalMap Q g z)
        (mfderiv (J (E := E)) (J (E := E))
          (sphereTotalMap Q g) z v)⟩ at h
  exact (Bundle.TotalSpace.ext_iff.mp h).2

theorem contactLineFiberMap_mul
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B)
    (f g : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) (v : L.core.Fiber z) :
    HEq (contactLineFiberMap Q D L (f * g) z v)
      (contactLineFiberMap Q D L f (sphereTotalMap Q g z)
        (contactLineFiberMap Q D L g z v)) := by
  obtain ⟨w, rfl⟩ := contactFormReal_surjective Q D L z v
  have hfg := contactLineFiberMap_contactFormReal Q D L (f * g) z w
  have hg := contactLineFiberMap_contactFormReal Q D L g z w
  have hf := contactLineFiberMap_contactFormReal Q D L f
    (sphereTotalMap Q g z)
    (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q g) z w)
  rw [hg, hf]
  have hform : HEq
      (L.contactFormReal Q D (sphereTotalMap Q (f * g) z)
        (mfderiv (J (E := E)) (J (E := E))
          (sphereTotalMap Q (f * g)) z w))
      (L.contactFormReal Q D (sphereTotalMap Q f (sphereTotalMap Q g z))
        (mfderiv (J (E := E)) (J (E := E))
          (sphereTotalMap Q f) (sphereTotalMap Q g z)
          (mfderiv (J (E := E)) (J (E := E))
            (sphereTotalMap Q g) z w))) := by
    let θ : TangentBundle (J (E := E)) (SphereBundleTotal Q) →
        Bundle.TotalSpace ℂ L.core.Fiber := fun p =>
      ⟨p.1, L.contactFormReal Q D p.1 p.2⟩
    have ht := congrFun (sphereTotalMap_tangentMap_mul Q f g)
      (⟨z, w⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q))
    have hθ := congrArg θ ht
    exact (Bundle.TotalSpace.ext_iff.mp hθ).2
  exact (heq_of_eq hfg).trans hform

def contactLineTotalMap
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B)
    (f : QuaternionicIsometries Q) :
    Bundle.TotalSpace ℂ L.core.Fiber → Bundle.TotalSpace ℂ L.core.Fiber :=
  fun p => ⟨sphereTotalMap Q f p.1,
    contactLineFiberMap Q D L f p.1 p.2⟩

theorem contactLineTotalMap_mul
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B)
    (f g : QuaternionicIsometries Q) :
    contactLineTotalMap Q D L (f * g) =
      contactLineTotalMap Q D L f ∘ contactLineTotalMap Q D L g := by
  funext ⟨z, v⟩
  apply Bundle.TotalSpace.ext
  · exact mul_smul f g z
  · exact contactLineFiberMap_mul Q D L f g z v

theorem contactSectionEquiv_mul
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f g : QuaternionicIsometries Q) :
    letI := B.charts
    contactSectionEquiv Q D B C (f * g) =
      (contactSectionEquiv Q D B C g).trans
        (contactSectionEquiv Q D B C f) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  apply LinearEquiv.ext
  intro s
  apply ContMDiffSection.ext
  intro y
  obtain ⟨z, rfl⟩ := (MulAction.toPerm (f * g)).surjective y
  apply (Bundle.TotalSpace.mk_injective (sphereTotalMap Q (f * g) z))
  have hfg := contactSectionEquiv_apply_at_image Q D B C (f * g) s z
  have hg := contactSectionEquiv_apply_at_image Q D B C g s z
  have hf := contactSectionEquiv_apply_at_image Q D B C f
    (contactSectionEquiv Q D B C g s) (sphereTotalMap Q g z)
  have htotal := congrFun (contactLineTotalMap_mul Q D C.line f g)
    (⟨z, s z⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber)
  calc
    (⟨sphereTotalMap Q (f * g) z,
      (contactSectionEquiv Q D B C (f * g) s)
        (sphereTotalMap Q (f * g) z)⟩ :
        Bundle.TotalSpace ℂ C.line.core.Fiber) =
      contactLineTotalMap Q D C.line (f * g) ⟨z, s z⟩ := by
        rw [hfg]
        rfl
    _ = (contactLineTotalMap Q D C.line f ∘
      contactLineTotalMap Q D C.line g) ⟨z, s z⟩ := htotal
    _ = ⟨sphereTotalMap Q (f * g) z,
      ((contactSectionEquiv Q D B C g).trans
        (contactSectionEquiv Q D B C f) s)
          (sphereTotalMap Q (f * g) z)⟩ := by
        have hbase : sphereTotalMap Q (f * g) z =
            sphereTotalMap Q f (sphereTotalMap Q g z) := mul_smul f g z
        rw [hbase]
        simp only [Function.comp_apply, LinearEquiv.trans_apply]
        rw [hf, hg]
        rfl

/-- The genuine complex-linear representation of actual quaternionic
isometries on all global holomorphic sections of the contact line. -/
def contactSectionRepresentation
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) :
    letI := B.charts
    QuaternionicIsometries Q →* Module.End ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line)) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  exact {
    toFun := fun f => (contactSectionEquiv Q D B C f).toLinearMap
    map_one' := by
      rw [contactSectionEquiv_one Q D B C]
      rfl
    map_mul' := by
      intro f g
      rw [contactSectionEquiv_mul Q D B C f g]
      rfl
  }

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryContactSectionAction
