import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Tactic

open Equiv.Perm

example (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [IsEmpty α] :
    shuffles α β = {1} := by
  exact?
