import Mathlib.GroupTheory.Perm.Shuffle

open Equiv.Perm

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

#check finset_shuffles_of_isEmpty_left
#check finset_shuffles_of_isEmpty_right
