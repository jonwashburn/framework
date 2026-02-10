import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Basic

example (n k : ℕ) : TopologicalSpace ((EuclideanSpace ℂ (Fin n)) [⋀^Fin k]→ₗ[ℝ] ℂ) := inferInstance
