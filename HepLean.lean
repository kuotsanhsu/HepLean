import HepLean.AnomalyCancellation.Basic
import HepLean.AnomalyCancellation.GroupActions
import HepLean.AnomalyCancellation.MSSMNu.B3
import HepLean.AnomalyCancellation.MSSMNu.Basic
import HepLean.AnomalyCancellation.MSSMNu.HyperCharge
import HepLean.AnomalyCancellation.MSSMNu.LineY3B3
import HepLean.AnomalyCancellation.MSSMNu.OrthogY3B3.Basic
import HepLean.AnomalyCancellation.MSSMNu.OrthogY3B3.PlaneWithY3B3
import HepLean.AnomalyCancellation.MSSMNu.OrthogY3B3.ToSols
import HepLean.AnomalyCancellation.MSSMNu.Permutations
import HepLean.AnomalyCancellation.MSSMNu.Y3
import HepLean.AnomalyCancellation.PureU1.Basic
import HepLean.AnomalyCancellation.PureU1.BasisLinear
import HepLean.AnomalyCancellation.PureU1.ConstAbs
import HepLean.AnomalyCancellation.PureU1.Even.BasisLinear
import HepLean.AnomalyCancellation.PureU1.Even.LineInCubic
import HepLean.AnomalyCancellation.PureU1.Even.Parameterization
import HepLean.AnomalyCancellation.PureU1.LineInPlaneCond
import HepLean.AnomalyCancellation.PureU1.LowDim.One
import HepLean.AnomalyCancellation.PureU1.LowDim.Three
import HepLean.AnomalyCancellation.PureU1.LowDim.Two
import HepLean.AnomalyCancellation.PureU1.Odd.BasisLinear
import HepLean.AnomalyCancellation.PureU1.Odd.LineInCubic
import HepLean.AnomalyCancellation.PureU1.Odd.Parameterization
import HepLean.AnomalyCancellation.PureU1.Permutations
import HepLean.AnomalyCancellation.PureU1.Sorts
import HepLean.AnomalyCancellation.PureU1.VectorLike
import HepLean.AnomalyCancellation.SM.Basic
import HepLean.AnomalyCancellation.SM.FamilyMaps
import HepLean.AnomalyCancellation.SM.NoGrav.Basic
import HepLean.AnomalyCancellation.SM.NoGrav.One.Lemmas
import HepLean.AnomalyCancellation.SM.NoGrav.One.LinearParameterization
import HepLean.AnomalyCancellation.SM.Permutations
import HepLean.AnomalyCancellation.SMNu.Basic
import HepLean.AnomalyCancellation.SMNu.FamilyMaps
import HepLean.AnomalyCancellation.SMNu.NoGrav.Basic
import HepLean.AnomalyCancellation.SMNu.Ordinary.Basic
import HepLean.AnomalyCancellation.SMNu.Ordinary.DimSevenPlane
import HepLean.AnomalyCancellation.SMNu.Ordinary.FamilyMaps
import HepLean.AnomalyCancellation.SMNu.Permutations
import HepLean.AnomalyCancellation.SMNu.PlusU1.BMinusL
import HepLean.AnomalyCancellation.SMNu.PlusU1.Basic
import HepLean.AnomalyCancellation.SMNu.PlusU1.BoundPlaneDim
import HepLean.AnomalyCancellation.SMNu.PlusU1.FamilyMaps
import HepLean.AnomalyCancellation.SMNu.PlusU1.HyperCharge
import HepLean.AnomalyCancellation.SMNu.PlusU1.PlaneNonSols
import HepLean.AnomalyCancellation.SMNu.PlusU1.QuadSol
import HepLean.AnomalyCancellation.SMNu.PlusU1.QuadSolToSol
import HepLean.BeyondTheStandardModel.GeorgiGlashow.Basic
import HepLean.BeyondTheStandardModel.PatiSalam.Basic
import HepLean.BeyondTheStandardModel.Spin10.Basic
import HepLean.BeyondTheStandardModel.TwoHDM.Basic
import HepLean.BeyondTheStandardModel.TwoHDM.GaugeOrbits
import HepLean.FeynmanDiagrams.Basic
import HepLean.FeynmanDiagrams.Instances.ComplexScalar
import HepLean.FeynmanDiagrams.Instances.Phi4
import HepLean.FeynmanDiagrams.Momentum
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Invariants
import HepLean.FlavorPhysics.CKMMatrix.PhaseFreedom
import HepLean.FlavorPhysics.CKMMatrix.Relations
import HepLean.FlavorPhysics.CKMMatrix.Rows
import HepLean.FlavorPhysics.CKMMatrix.StandardParameterization.Basic
import HepLean.FlavorPhysics.CKMMatrix.StandardParameterization.StandardParameters
import HepLean.Lorentz.Algebra.Basic
import HepLean.Lorentz.Algebra.Basis
import HepLean.Lorentz.ComplexTensor.Basic
import HepLean.Lorentz.ComplexTensor.Basis
import HepLean.Lorentz.ComplexTensor.Bispinors.Basic
import HepLean.Lorentz.ComplexTensor.Lemmas
import HepLean.Lorentz.ComplexTensor.Metrics.Basic
import HepLean.Lorentz.ComplexTensor.Metrics.Basis
import HepLean.Lorentz.ComplexTensor.Metrics.Lemmas
import HepLean.Lorentz.ComplexTensor.PauliMatrices.Basic
import HepLean.Lorentz.ComplexTensor.PauliMatrices.Basis
import HepLean.Lorentz.ComplexTensor.PauliMatrices.CoContractContr
import HepLean.Lorentz.ComplexTensor.Units.Basic
import HepLean.Lorentz.ComplexTensor.Units.Symm
import HepLean.Lorentz.ComplexVector.Basic
import HepLean.Lorentz.ComplexVector.Contraction
import HepLean.Lorentz.ComplexVector.Metric
import HepLean.Lorentz.ComplexVector.Modules
import HepLean.Lorentz.ComplexVector.Two
import HepLean.Lorentz.ComplexVector.Unit
import HepLean.Lorentz.Group.Basic
import HepLean.Lorentz.Group.Boosts
import HepLean.Lorentz.Group.Orthochronous
import HepLean.Lorentz.Group.Proper
import HepLean.Lorentz.Group.Restricted
import HepLean.Lorentz.Group.Rotations
import HepLean.Lorentz.MinkowskiMatrix
import HepLean.Lorentz.PauliMatrices.AsTensor
import HepLean.Lorentz.PauliMatrices.Basic
import HepLean.Lorentz.PauliMatrices.SelfAdjoint
import HepLean.Lorentz.RealVector.Basic
import HepLean.Lorentz.RealVector.Contraction
import HepLean.Lorentz.RealVector.Modules
import HepLean.Lorentz.RealVector.NormOne
import HepLean.Lorentz.SL2C.Basic
import HepLean.Lorentz.Weyl.Basic
import HepLean.Lorentz.Weyl.Contraction
import HepLean.Lorentz.Weyl.Metric
import HepLean.Lorentz.Weyl.Modules
import HepLean.Lorentz.Weyl.Two
import HepLean.Lorentz.Weyl.Unit
import HepLean.Mathematics.Fin
import HepLean.Mathematics.LinearMaps
import HepLean.Mathematics.PiTensorProduct
import HepLean.Mathematics.SO3.Basic
import HepLean.Meta.AllFilePaths
import HepLean.Meta.Basic
import HepLean.Meta.Informal
import HepLean.Meta.TransverseTactics
import HepLean.SpaceTime.Basic
import HepLean.SpaceTime.CliffordAlgebra
import HepLean.StandardModel.Basic
import HepLean.StandardModel.HiggsBoson.Basic
import HepLean.StandardModel.HiggsBoson.GaugeAction
import HepLean.StandardModel.HiggsBoson.PointwiseInnerProd
import HepLean.StandardModel.HiggsBoson.Potential
import HepLean.StandardModel.Representations
import HepLean.Tensors.OverColor.Basic
import HepLean.Tensors.OverColor.Discrete
import HepLean.Tensors.OverColor.Functors
import HepLean.Tensors.OverColor.Iso
import HepLean.Tensors.OverColor.Lift
import HepLean.Tensors.TensorSpecies.Basic
import HepLean.Tensors.Tree.Basic
import HepLean.Tensors.Tree.Dot
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.Tree.NodeIdentities.Basic
import HepLean.Tensors.Tree.NodeIdentities.Congr
import HepLean.Tensors.Tree.NodeIdentities.ContrContr
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.PermContr
import HepLean.Tensors.Tree.NodeIdentities.PermProd
import HepLean.Tensors.Tree.NodeIdentities.ProdAssoc
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.ProdContr
