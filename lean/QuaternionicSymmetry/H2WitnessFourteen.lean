import QuaternionicSymmetry.H2WitnessThirteen

/-! A complete finite rational witness for the dimension-fourteen density.
This is a newly recovered witness with scalar reserve 448; it does not
verify the omitted Gram data of the textbook's earlier H2 claim. -/

namespace QuaternionicSymmetry.H2WitnessFourteen

open MvPolynomial
open FiniteTypeCSchurSix
noncomputable section
set_option maxHeartbeats 2500000

abbrev P := FiniteTypeCSchurSix.P

def w1 : P :=
  C (23680744832 / 675675 : ℚ) * orbital 14 1 [1]

def w2 : P :=
  C (171676659316 / 1674848175 : ℚ) * orbital 14 2 [50, 1]
    + C (17216030238103 / 19897196319 : ℚ) * orbital 14 2 [5, 5, 4, 3, 3, 2]

def w3 : P :=
  C (273783296517568 / 672296625 : ℚ) * orbital 14 3 [2, 2, 1]
    + C (46347112829804 / 80675595 : ℚ) * orbital 14 3 [1, 1, 1, 1]
    + C (1484602223596 / 288127125 : ℚ) * orbital 14 3 [5, 3, 3, 3, 3, 1, 1, 1]

def w4 : P :=
  C (356808331361902532433624693713 / 37332699024560940000000 : ℚ) * orbital 14 4 [1, 1, 1]
    + C (127495476249371257585032337 / 1866634951228047000000000 : ℚ) * orbital 14 4 [20, 20, 20, 1, 1, 1, 1, 1]
    + C (122169414208022993203547391499 / 25199571841578634500000000 : ℚ) * orbital 14 4 [10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    + C (2494744228248597073220802007 / 2015965747326290760000000 : ℚ) * orbital 14 4 [10, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    + C (4837968937363248196357649 / 24888466016373960000000 : ℚ) * orbital 14 4 [20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def w5 : P :=
  C (66425800394330667209269014307960 / 2158186208921284109709141 : ℚ) * orbital 14 5 [1, 1, 1]
    + C (14177200569401784892753879755658 / 5994961691448011415858725 : ℚ) * orbital 14 5 [4, 1, 1, 1, 1]
    + C (10615050899403199814419057598 / 700709808091326009645825 : ℚ) * orbital 14 5 [7, 1, 1, 1, 1, 1]
    + C (11705729862598199204367895328 / 161863965669096308228185575 : ℚ) * orbital 14 5 [20, 20, 1, 1, 1, 1, 1, 1]
    + C (1931899571750201774241699455512 / 269773276115160513713642625 : ℚ) * orbital 14 5 [10, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    + C (428766438320297179182003308488 / 5665238798418370787986495125 : ℚ) * orbital 14 5 [20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    + C (1225410205325640489589309598 / 23123423667013758318312225 : ℚ) * orbital 14 5 [20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def w6 : P :=
  C (143165778678727315577100302989967862553190190411890616611 / 13538193449181579688147426271630700000000000000000 : ℚ) * orbital 14 6 [2, 1]
    + C (30108004661665175052607763476328586914084097175449594871 / 5479744967525877492821577300421950000000000000000 : ℚ) * orbital 14 6 [3, 1]
    + C (7925048720206486642385289299606499841386824073239482372319 / 230149288636086854698506246617721900000000000000000 : ℚ) * orbital 14 6 [1, 1, 1]
    + C (7904185324346295923596513556450109864952395212499119 / 5415277379672631875258970508652280000000000000000 : ℚ) * orbital 14 6 [13, 4, 3]
    + C (794300393518454199293023657035292225075709414701143590603 / 805522510226303991444771863162026650000000000000000 : ℚ) * orbital 14 6 [1, 1, 1, 1, 1]
    + C (189659299265698663493575850330116572066642545499151733 / 7671642954536228489950208220590730000000000000000 : ℚ) * orbital 14 6 [11, 4, 2, 1, 1, 1]
    + C (945271277695911598512837768333383198960259974816453 / 2001298162052929171291358666241060000000000000000 : ℚ) * orbital 14 6 [15, 2, 1, 1, 1, 1]
    + C (616011666803318092230596046586234060566011034931782349 / 537015006817535994296514575441351100000000000000000 : ℚ) * orbital 14 6 [7, 7, 1, 1, 1, 1, 1]
    + C (23312416219410482719862006390327939304072498738107963 / 19179107386340571224875520551476825000000000000000 : ℚ) * orbital 14 6 [12, 2, 2, 1, 1, 1, 1, 1]
    + C (2991811056066578951260518660513141612851619092830597 / 613731436362898279196016657647258400000000000000000 : ℚ) * orbital 14 6 [20, 20, 1, 1, 1, 1, 1, 1, 1, 1]
    + C (20423584410265784907068635569039992351910060708735919 / 920597154544347418794024986470887600000000000000000 : ℚ) * orbital 14 6 [20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def f1 : P := p1
def f3 : P := C (88656 / 1000000000 : ℚ) * p3 +
  C (251370 / 1000000000 : ℚ) * p1 * p2 +
  C (223959 / 1000000000 : ℚ) * p1 ^ 3

private theorem weight_one :
    w1 = C (816577408 / 4729725 : ℚ) * p1 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w1, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, p1, Nat.factorial]
  ring

private theorem weight_two :
    w2 + C (20 : ℚ) * f1 ^ 2 =
      C (152085968 / 5457375 : ℚ) * p1 ^ 2 +
        C (620496752 / 212837625 : ℚ) * p2 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w2, f1, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, e1, e2,
    p1, p2, Nat.factorial]
  ring

private theorem weight_three :
    w3 = C (655424 / 273375 : ℚ) * p1 ^ 3 +
      C (46487872 / 49116375 : ℚ) * p1 * p2 +
      C (10779136 / 383107725 : ℚ) * p3 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w3, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, h3, e1, e2, e3,
    p1, p2, p3, Nat.factorial]
  ring

private theorem weight_four :
    w4 + C (40 : ℚ) * f1 * f3 =
      C (4904 / 42525 : ℚ) * p1 ^ 4 +
        C (23024 / 212625 : ℚ) * p1 ^ 2 * p2 +
        C (36256 / 4465125 : ℚ) * p2 ^ 2 +
        C (1084576 / 49116375 : ℚ) * p1 * p3 -
        C (170152 / 212837625 : ℚ) * p4 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w4, f1, f3, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, h3, h4,
    e1, e2, e3, e4, p1, p2, p3, p4, Nat.factorial]
  ring

private theorem weight_five :
    w5 = C (32 / 10935 : ℚ) * p1 ^ 5 +
      C (2008 / 382725 : ℚ) * p1 ^ 3 * p2 +
      C (184 / 76545 : ℚ) * p1 ^ 2 * p3 +
      C (296 / 212625 : ℚ) * p1 * p2 ^ 2 +
      C (1648 / 2338875 : ℚ) * p1 * p4 +
      C (5512 / 13395375 : ℚ) * p2 * p3 +
      C (3712 / 70945875 : ℚ) * p5 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w5, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, h3, h4, h5,
    e1, e2, e3, e4, e5, p1, p2, p3, p4, p5, Nat.factorial]
  ring

private theorem weight_six :
    w6 + C (20 : ℚ) * f3 ^ 2 =
      C (1 / 32805 : ℚ) * p1 ^ 6 +
        C (1 / 10935 : ℚ) * p1 ^ 4 * p2 +
        C (16 / 229635 : ℚ) * p1 ^ 3 * p3 +
        C (1 / 18225 : ℚ) * p1 ^ 2 * p2 ^ 2 +
        C (2 / 42525 : ℚ) * p1 ^ 2 * p4 +
        C (16 / 382725 : ℚ) * p1 * p2 * p3 +
        C (32 / 1403325 : ℚ) * p1 * p5 +
        C (1 / 273375 : ℚ) * p2 ^ 3 +
        C (2 / 212625 : ℚ) * p2 * p4 +
        C (32 / 8037225 : ℚ) * p3 ^ 2 +
        C (11056 / 1915538625 : ℚ) * p6 := by
  apply MvPolynomial.funext
  intro v
  norm_num [w6, f3, orbital, partitions, schurValue, schur, powerSum,
    QuarticOrbitalEleven.factorialRho, h1, h2, h3, h4, h5, h6,
    e1, e2, e3, e4, e5, e6, p1, p2, p3, p4, p5, p6, Nat.factorial]
  ring

def embed : P →ₐ[ℚ] DimensionThirteenFourteenDensity.P :=
  H2WitnessThirteen.embed

def factor : DimensionThirteenFourteenDensity.P :=
  DimensionThirteenFourteenDensity.u ^ 2 * embed f1 + embed f3

def orbitalSum : DimensionThirteenFourteenDensity.P :=
  DimensionThirteenFourteenDensity.u ^ 13 * embed w1 +
    DimensionThirteenFourteenDensity.u ^ 12 * embed w2 +
    DimensionThirteenFourteenDensity.u ^ 11 * embed w3 +
    DimensionThirteenFourteenDensity.u ^ 10 * embed w4 +
    DimensionThirteenFourteenDensity.u ^ 9 * embed w5 +
    DimensionThirteenFourteenDensity.u ^ 8 * embed w6

def witness : DimensionThirteenFourteenDensity.P :=
  C 448 * DimensionThirteenFourteenDensity.u ^ 14 + orbitalSum +
    C 20 * factor ^ 2 * DimensionThirteenFourteenDensity.u ^ 8

theorem density14_witness : DimensionThirteenFourteenDensity.density14 = witness := by
  rw [DimensionThirteenFourteenDensity.density14_printed]
  unfold witness orbitalSum factor
  rw [weight_one]
  have h2 := congrArg embed weight_two
  have h3 := congrArg embed weight_three
  have h4 := congrArg embed weight_four
  have h5 := congrArg embed weight_five
  have h6 := congrArg embed weight_six
  simp only [map_add, map_sub, map_mul, map_pow] at h2 h3 h4 h5 h6
  simp only [DimensionThirteenFourteenDensity.printed14,
    DimensionThirteenFourteenDensity.q14]
  simp [embed, H2WitnessThirteen.embed, p1, p2, p3, p4, p5, p6,
    DimensionThirteenFourteenDensity.p1, DimensionThirteenFourteenDensity.p2,
    DimensionThirteenFourteenDensity.p3, DimensionThirteenFourteenDensity.p4,
    DimensionThirteenFourteenDensity.p5, DimensionThirteenFourteenDensity.p6] at h2 h3 h4 h5 h6 ⊢
  simp only [map_ofNat] at h2 h3 h4 h5 h6 ⊢
  linear_combination
    -(DimensionThirteenFourteenDensity.u ^ 12) * h2 -
    DimensionThirteenFourteenDensity.u ^ 11 * h3 -
    DimensionThirteenFourteenDensity.u ^ 10 * h4 -
    DimensionThirteenFourteenDensity.u ^ 9 * h5 -
    DimensionThirteenFourteenDensity.u ^ 8 * h6

end
end QuaternionicSymmetry.H2WitnessFourteen
