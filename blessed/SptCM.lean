module

public import blessed.SptCM.Definitions
public import blessed.SptCM.PaperInterfaces
public import blessed.SptCM.Analytic.ThetaHecke
public import blessed.SptCM.Analytic.DualityPairing
public import blessed.SptCM.Analytic.ProductObstruction
public import blessed.SptCM.Analytic.PaperCoefficientModels
public import blessed.SptCM.Analytic.PaperConstructions
public import blessed.SptCM.Analytic.Repaired.Duality
public import blessed.SptCM.Analytic.Repaired.GaussSum
public import blessed.SptCM.Analytic.Repaired.GridHeckePrincipalParts
public import blessed.SptCM.Analytic.Repaired.GridNormalization
public import blessed.SptCM.Analytic.Repaired.EulerProducts
public import blessed.SptCM.Analytic.Repaired.PairingBorcherds
public import blessed.SptCM.Analytic.Repaired.I12NormalizedProduct
public import blessed.SptCM.Analytic.Repaired.WeilGenerators
public import blessed.SptCM.Analytic.Repaired.HeckePrincipalParts
public import blessed.SptCM.Analytic.Repaired.VectorFourierData
public import blessed.SptCM.Analytic.Repaired.CuspEnumeration
public import blessed.SptCM.Analytic.Repaired.StokesConstantTerm
public import blessed.SptCM.Analytic.Repaired.CuspContractions
public import blessed.SptCM.Analytic.Repaired.CuspWeylVectors
public import blessed.SptCM.Analytic.Repaired.I05HeckeApplication
public import blessed.SptCM.Analytic.Repaired.CharacteristicGridSupport
public import blessed.SptCM.Analytic.Repaired.SquareCoefficientVanishing
public import blessed.SptCM.Analytic.Repaired.UniformNormalizedProduct
public import blessed.SptCM.Arithmetic.SmallDiscriminant
public import blessed.SptCM.Arithmetic.Repaired.ClassNumberOrientation
public import blessed.SptCM.CM.ClassPolynomials
public import blessed.SptCM.CM.Repaired.HauptmodulCoordinate
public import blessed.SptCM.CM.Repaired.ActualCMValues
public import blessed.SptCM.CM.Repaired.ActualCoordinateConstruction
public import blessed.SptCM.CM.Repaired.GaloisPolynomialDescent
public import blessed.SptCM.CM.Repaired.OrientedClassActions
public import blessed.SptCM.CM.Repaired.I16Coordinates
public import blessed.SptCM.CM.Repaired.I16Reduction
public import blessed.SptCM.CM.Repaired.I18RootSpecialization
public import blessed.SptCM.CM.Repaired.I18CommonRoot
public import blessed.SptCM.CM.Reduction
public import blessed.SptCM.CM.ActualClassPolynomials
public import blessed.SptCM.CM.Borcherds
public import blessed.SptCM.Literature.RolenLiterature
public import blessed.SptCM.Literature.Repair.UniformLedger
public import blessed.SptCM.Literature.Repair.PublicLedger
public import blessed.SptCM.Repair.AdmissibleRange
public import blessed.SptCM.Repair.ActualLaurentBridge
public import blessed.SptCM.Repair.AnalyticFormalIdentification
public import blessed.SptCM.Repair.I15ActualApplication
public import blessed.SptCM.Repair.I15ActualCoordinate
public import blessed.SptCM.Repair.I21ActualLaurentModel
public import blessed.SptCM.Repair.I12WronskianZero
public import blessed.SptCM.Repair.AndrewsCongruences
public import blessed.SptCM.Repair.CMPolynomialReduction
public import blessed.SptCM.Repair.FinalAssembly
public import blessed.SptCM.Repair.FormalHauptmodulEuler
public import blessed.SptCM.Repair.GridSupport
public import blessed.SptCM.Repair.LaurentHauptmodul
public import blessed.SptCM.Repair.MinimalInert
public import blessed.SptCM.Repair.SignedExponent
public import blessed.SptCM.Repair.SoundObstruction
public import blessed.SptCM.Repair.TrevinoBridge
public import blessed.SptCM.Repair.WronskianAssembly
public import blessed.SptCM.Quaternion.Separation
public import blessed.SptCM.Quaternion.Repaired.CommonRootSeparation
public import blessed.SptCM.Quaternion.Repaired.NormHadamard
public import blessed.SptCM.Quaternion.Repaired.I20Covolume
public import blessed.SptCM.Quaternion.Repaired.ActualSeparation
public import blessed.SptCM.Quaternion.Repaired.I19ActualAdapter
public import blessed.SptCM.Quaternion.Repaired.ActualPointConstruction
public import blessed.SptCM.Lemmas.Polynomial
public import blessed.SptCM.Lemmas.SmallDiscriminantArithmetic
public import blessed.SptCM.Lemmas.VolumeArithmetic
public import blessed.SptCM.Interfaces
public import blessed.SptCM.Main
public import blessed.SptCM.PaperMain
public import blessed.SptCM.Solution

public import blessed.SptCM.Repair.ActualWronskianContradiction
public import blessed.SptCM.Repair.PublicLargeExclusion

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

