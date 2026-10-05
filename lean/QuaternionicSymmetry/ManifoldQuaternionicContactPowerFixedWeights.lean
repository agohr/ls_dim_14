import QuaternionicSymmetry.ManifoldQuaternionicContactPowerWeights

/-! At a genuine torus-fixed twistor point, a generating contact power has
a nonzero eigenbasis evaluation. Its actual fiber scalar is consequently
one of the complete section representation's characters. This is a literal
fiber/evaluation comparison; neither a fixed point nor global generation of
the unpowered contact line is assumed to follow from mere ampleness. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerFixedWeights

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactPowerSections
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactPowerContinuity ManifoldQuaternionicContactPowerWeights
open ManifoldQuaternionicTorusAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open HolomorphicLineCoreProjectiveEvaluation
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem exists_basis_section_nonzero
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    {ι : Type*} (b : letI := B.charts; Module.Basis ι ℂ (PowerSections Q D B C k))
    (hGen : letI := B.charts
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k))
    (z : SphereBundleTotal Q) : ∃ i : ι, b i z ≠ 0 := by
  letI := B.charts
  by_contra hn
  push_neg at hn
  obtain ⟨s,hs⟩ := hGen z
  have heval : evaluation 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k) z = 0 := by
    apply b.ext
    intro i
    exact hn i
  exact hs (congrArg (fun F : Module.Dual ℂ (PowerSections Q D B C k) => F s) heval)

theorem fixedPoint_powerScalar_eq_eigencharacter
    {r : ℕ} (T : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (s : letI := B.charts; PowerSections Q D B C k)
    (μ : Fin r → ℤ)
    (hEigen : letI := B.charts
      ∀ t : Torus r, contactPowerTorusRepresentation Q T D B C k t s =
        (weightCharacter μ t : ℂ) • s)
    (z : SphereBundleTotal Q)
    (hFixed : ∀ t : Torus r, sphereTotalMap Q (T.representation t) z = z)
    (hs : s z ≠ 0) (t : Torus r) :
    contactScalar Q D C.line (T.representation t) z ^ k = (weightCharacter μ t : ℂ) := by
  letI := B.charts
  let ev : PowerSections Q D B C k → SphereBundleTotal Q → ℂ := fun a x => a x
  have hImage : ev (contactPowerTorusRepresentation Q T D B C k t s)
      (sphereTotalMap Q (T.representation t) z) =
      contactScalar Q D C.line (T.representation t) z ^ k * ev s z :=
    contactPowerSectionEquiv_apply_at_image Q D B C (T.representation t) k s z
  rw [hFixed t] at hImage
  have hValue : ev (contactPowerTorusRepresentation Q T D B C k t s) z =
      (weightCharacter μ t : ℂ) * ev s z :=
    congrArg (fun a : PowerSections Q D B C k => ev a z) (hEigen t)
  exact mul_right_cancel₀ hs (hImage.symm.trans hValue)

theorem exists_eigencharacter_at_fixedPoint
    {r : ℕ} (T : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    {ι : Type*} (b : letI := B.charts; Module.Basis ι ℂ (PowerSections Q D B C k))
    (μ : ι → Fin r → ℤ)
    (hEigen : letI := B.charts
      ∀ (t : Torus r) (i : ι), contactPowerTorusRepresentation Q T D B C k t (b i) =
        (weightCharacter (μ i) t : ℂ) • b i)
    (hGen : letI := B.charts
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k))
    (z : SphereBundleTotal Q)
    (hFixed : ∀ t : Torus r, sphereTotalMap Q (T.representation t) z = z) :
    ∃ i : ι, b i z ≠ 0 ∧ ∀ t : Torus r,
      contactScalar Q D C.line (T.representation t) z ^ k =
        (weightCharacter (μ i) t : ℂ) := by
  obtain ⟨i,hi⟩ := exists_basis_section_nonzero Q D B C k b hGen z
  exact ⟨i,hi,fun t => fixedPoint_powerScalar_eq_eigencharacter Q T D B C k
    (b i) (μ i) (fun t => hEigen t i) z hFixed hi t⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerFixedWeights
