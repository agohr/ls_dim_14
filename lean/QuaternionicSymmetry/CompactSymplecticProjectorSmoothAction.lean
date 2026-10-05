import QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric
import QuaternionicSymmetry.CompactSymplecticHomogeneousAtlasSource
import QuaternionicSymmetry.GeneralSmoothMapSource
import QuaternionicSymmetry.ManifoldImmersionSmooth
import QuaternionicSymmetry.ManifoldEquivariantPullbackPairing
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-! Smoothness of the actual matrix conjugation action in the Lee Lie atlas.
The smooth matrix-unit inclusion is supplied by the chosen embedded atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorSmoothAction

open Matrix Manifold CompactSymplecticHaar
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticMatrixUnits
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectiveQuotient
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticProjectorAmbientMetric
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n
private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- The actual matrix-unit inclusion is smooth in the Lee atlas. The proof
uses the immersion chart normal form, avoiding Mathlib's incomplete
`IsSmoothEmbedding.contMDiff` interface. -/
theorem smooth_matrix_inclusion (n d : ℕ) (g : EmbeddedRealLieAtlas n d) :
    letI := g.charts
    ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
      (toMatrixUnits n) := by
  letI := g.charts
  letI := g.manifold
  exact ManifoldImmersionSmooth.smoothEmbedding_contMDiff g.smoothEmbedding

/-- Smooth ambient matrix multiplication in its actual real Banach model. -/
private theorem smooth_matrix_mul (n : ℕ) :
    ContMDiff (𝓘(ℝ, Mat n).prod 𝓘(ℝ, Mat n)) 𝓘(ℝ, Mat n) ∞
      (fun p : Mat n × Mat n => p.1 * p.2) := by
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact contDiff_mul.contMDiff

/-- The concrete smooth matrix representation of the chosen Lee Lie group. -/
theorem smooth_group_matrix (n d : ℕ) (g : EmbeddedRealLieAtlas n d)
    (hIncl : letI := g.charts
      ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
        (toMatrixUnits n)) :
    letI := g.charts
    ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
      (fun u : G n => (u.1 : Mat n)) := by
  letI := g.charts
  change ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
    ((Units.val : (Mat n)ˣ → Mat n) ∘ toMatrixUnits n)
  exact Units.contMDiff_val.comp hIncl

/-- The actual compact symplectic action on all ambient matrices is smooth. -/
theorem smooth_conjugation (n d : ℕ) (g : EmbeddedRealLieAtlas n d)
    (hIncl : letI := g.charts
      ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
        (toMatrixUnits n)) :
    letI := g.charts
    ContMDiff (𝓘(ℝ, RModel d).prod 𝓘(ℝ, Mat n))
      𝓘(ℝ, Mat n) ∞
      (fun p : G n × Mat n =>
        (p.1.1 : Mat n) * p.2 * ((p.1⁻¹).1 : Mat n)) := by
  letI := g.charts
  letI := g.manifold
  letI := g.lieGroup
  have hu := smooth_group_matrix n d g hIncl
  have huInv : ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
      (fun u : G n => ((u⁻¹).1 : Mat n)) := by
    exact hu.comp (contMDiff_inv 𝓘(ℝ, RModel d) ∞)
  have hleft : ContMDiff (𝓘(ℝ, RModel d).prod 𝓘(ℝ, Mat n))
      𝓘(ℝ, Mat n) ∞ (fun p : G n × Mat n => (p.1.1 : Mat n) * p.2) := by
    exact (smooth_matrix_mul n).comp ((hu.comp contMDiff_fst).prodMk contMDiff_snd)
  exact (smooth_matrix_mul n).comp
    (hleft.prodMk (huInv.comp contMDiff_fst))

/-- The actual first-pair projector orbit map is smooth in the selected
Lee atlas of the compact matrix group. -/
theorem smooth_orbitProjector (n d : ℕ) (g : EmbeddedRealLieAtlas n d)
    (hIncl : letI := g.charts
      ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
        (toMatrixUnits n)) :
    letI := g.charts
    ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
      (orbitProjector n) := by
  letI := g.charts
  have hpair : ContMDiff 𝓘(ℝ, RModel d)
      (𝓘(ℝ, RModel d).prod 𝓘(ℝ, Mat n)) ∞
      (fun u : G n => (u, firstPairProjector n)) := by
    exact contMDiff_id.prodMk contMDiff_const
  have h := (smooth_conjugation n d g hIncl).comp hpair
  convert h using 1

/-- Lee's general submersion theorem descends smoothness to the actual
projector map on the chosen smooth coset quotient. -/
theorem smooth_quotientOrbitProjector
    (hLee : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (hIncl : letI := g.charts
      ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
        (toMatrixUnits n)) :
    letI := a.quotientCharts
    ContMDiff 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n) ∞
      (quotientOrbitProjector n) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI : SecondCountableTopology (Mat n)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (G n) :=
    (toMatrixUnits_closedEmbedding n).isEmbedding.secondCountableTopology
  have hComp : ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, Mat n) ∞
      ((quotientOrbitProjector n) ∘ (fun u : G n => (u : ProjectiveCarrier n))) := by
    simpa only [Function.comp_def, quotientOrbitProjector_mk] using
      smooth_orbitProjector n d g hIncl
  exact hLee (fun u : G n => (u : ProjectiveCarrier n))
    (quotientOrbitProjector n)
    (by intro x; induction x using Quotient.inductionOn' with | _ u => exact ⟨u, rfl⟩)
    a.quotientSmooth a.quotientSubmersive hComp

/-- The projector map on the selected Lee quotient is genuinely smooth,
with no specialized smoothness premise. -/
theorem smooth_quotientOrbitProjector_actual
    (hLee : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    ContMDiff 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n) ∞
      (quotientOrbitProjector n) :=
  smooth_quotientOrbitProjector hLee n d e q g a
    (smooth_matrix_inclusion n d g)

/-- The selected Lee quotient carries the actual smooth transitive coset
action, in the form required by the general equivariant immersion theorem. -/
def smoothCarrierAction (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := g.charts
    letI := a.quotientCharts
    GeneralSmoothMapSource.SmoothLeftAction (RModel d) (RModel q)
      (G n) (ProjectiveCarrier n) := by
  letI := g.charts
  letI := a.quotientCharts
  letI : MulAction.QuotientAction (G n) (K n) :=
    MulAction.left_quotientAction (K n)
  letI : MulAction (G n) (ProjectiveCarrier n) :=
    MulAction.quotient (G n) (K n)
  refine {
    act := leftCosetAction n
    one_act := ?_
    mul_act := ?_
    smooth := a.actionSmooth
  }
  · intro x
    exact one_smul (G n) x
  · intro u v x
    exact SemigroupAction.mul_smul u v x

/-- The same group acts smoothly on the full ambient matrix vector space
by its actual matrix conjugation representation. -/
def smoothAmbientAction (n d : ℕ) (g : EmbeddedRealLieAtlas n d) :
    letI := g.charts
    GeneralSmoothMapSource.SmoothLeftAction (RModel d) (Mat n)
      (G n) (Mat n) := by
  letI := g.charts
  letI := g.manifold
  letI := g.lieGroup
  refine {
    act := fun u A => (u.1 : Mat n) * A * (u.1 : Mat n)ᴴ
    one_act := ?_
    mul_act := ?_
    smooth := ?_
  }
  · intro A
    change (1 : Mat n) * A * (1 : Mat n)ᴴ = A
    simp
  · intro u v A
    change ((u.1 : Mat n) * (v.1 : Mat n)) * A *
      ((u.1 : Mat n) * (v.1 : Mat n))ᴴ =
      (u.1 : Mat n) * ((v.1 : Mat n) * A * (v.1 : Mat n)ᴴ) *
        (u.1 : Mat n)ᴴ
    rw [Matrix.conjTranspose_mul]
    simp only [mul_assoc]
  · convert smooth_conjugation n d g (smooth_matrix_inclusion n d g) using 1

/-- The actual left coset action is transitive on the quotient carrier. -/
theorem carrier_action_transitive (n : ℕ) (x y : ProjectiveCarrier n) :
    ∃ u : G n, leftCosetAction n u x = y := by
  induction x using Quotient.inductionOn' with
  | _ v =>
    induction y using Quotient.inductionOn' with
    | _ w =>
      refine ⟨w * v⁻¹, ?_⟩
      change (((w * v⁻¹) * v : G n) : ProjectiveCarrier n) = w
      simp

/-- The actual projector quotient map intertwines the coset and full
ambient matrix actions. -/
theorem quotient_projector_equivariant (n : ℕ) (u : G n)
    (x : ProjectiveCarrier n) :
    quotientOrbitProjector n (leftCosetAction n u x) =
      (u.1 : Mat n) * quotientOrbitProjector n x * (u.1 : Mat n)ᴴ := by
  induction x using Quotient.inductionOn' with
  | _ v =>
    change orbitProjector n (u * v) =
      (u.1 : Mat n) * orbitProjector n v * (u.1 : Mat n)ᴴ
    exact orbitProjector_mul n u v

/-- The genuine quotient-to-projector map has injective derivative at every
point. This specializes Lee's equivariant immersion theorem using the actual
transitive coset action, smooth matrix conjugation, and checked injectivity. -/
theorem quotientOrbitProjector_mfderiv_injective
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    Function.Injective
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x) := by
  letI := g.charts
  letI := g.manifold
  letI := g.lieGroup
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI : SecondCountableTopology (Mat n)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (G n) :=
    (toMatrixUnits_closedEmbedding n).isEmbedding.secondCountableTopology
  exact hImm (smoothCarrierAction n d e q g a)
    (smoothAmbientAction n d g) (quotientOrbitProjector n)
    (carrier_action_transitive n)
    (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
    (quotient_projector_equivariant n)
    (quotientOrbitProjector_injective n) x

/-- The literal derivative pullback of the Frobenius pairing is invariant
under the actual left action on the chosen Lee quotient. -/
theorem projector_pullback_pairing_invariant
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (u : G n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    ∀ (v w : TangentSpace 𝓘(ℝ, RModel q) x),
    frobeniusCLM n
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (leftCosetAction n u x)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n u) x v))
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (leftCosetAction n u x)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n u) x w)) =
    frobeniusCLM n
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x v)
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) x w) := by
  letI := g.charts
  letI := a.quotientCharts
  letI := a.quotientManifold
  intro v w
  have hAct : ContMDiff 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q) ∞
      (leftCosetAction n u) := by
    have hpair : ContMDiff 𝓘(ℝ, RModel q)
        (𝓘(ℝ, RModel d).prod 𝓘(ℝ, RModel q)) ∞
        (fun x : ProjectiveCarrier n => (u,x)) := by
      exact contMDiff_const.prodMk contMDiff_id
    exact a.actionSmooth.comp hpair
  exact ManifoldEquivariantPullbackPairing.pullback_pairing_invariant
    (quotientOrbitProjector n) (leftCosetAction n u)
    (conjugationCLM n u)
    (smooth_quotientOrbitProjector_actual hDesc n d e q g a)
    hAct (quotient_projector_equivariant n u)
    (frobeniusCLM n)
    (frobeniusCLM_conjugationCLM n u) x v w

end
end QuaternionicSymmetry.CompactSymplecticProjectorSmoothAction
