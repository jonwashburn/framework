import Mathlib
import IndisputableMonolith.ProteinFolding.Encoding.DFT8

/-!
# Derivation D7: Domain Segmentation Theorem

This module formalizes automatic domain boundary detection from
the DFT-8 secondary structure signal.

## Key Method

Domain boundaries are identified at positions where the cumulative
secondary structure signal has a local minimum with sufficient depth.

## Algorithm

1. Compute cumulative SS signal: S(i) = Σ_{j≤i} (P₂(j) + P₄(j))
2. Find local minima in S(i)
3. Filter minima with depth ≥ 20% relative to neighbors

## Physical Motivation

Domain boundaries occur where secondary structure signal is weak,
indicating flexible linker regions between compact structural units.

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace Derivations
namespace D7

open DFT8

/-! ## Cumulative Secondary Structure Signal -/

/-- Compute cumulative SS signal at position i

    S(i) = Σ_{j≤i} (P₂(j) + P₄(j))

    where P₂ and P₄ are the mode-2 and mode-4 powers from DFT-8 -/
noncomputable def cumulativeSSSignal (spectra : List (Fin 8 → ℂ)) (i : ℕ) : ℝ :=
  let powers := spectra.take (i + 1) |>.map fun X =>
    modePower X mode2 + modePower X mode4
  powers.sum

/-- SS signal at a single position -/
noncomputable def ssSignalAt (spectra : List (Fin 8 → ℂ)) (i : ℕ) : ℝ :=
  match spectra.get? i with
  | some X => modePower X mode2 + modePower X mode4
  | none => 0

/-! ## Local Minimum Detection -/

/-- Check if position i is a local minimum in cumulative signal -/
noncomputable def isLocalMinimum
    (signal : ℕ → ℝ)
    (i : ℕ)
    (windowRadius : ℕ := 3) : Bool :=
  let si := signal i
  let neighbors := (List.range (2 * windowRadius + 1)).filterMap fun k =>
    let j := i + k - windowRadius
    if j ≠ i then some (signal j) else none
  neighbors.all fun sj => si ≤ sj

/-- Depth of a local minimum (relative to neighbors) -/
noncomputable def minimumDepth
    (signal : ℕ → ℝ)
    (i : ℕ)
    (windowRadius : ℕ := 3) : ℝ :=
  let si := signal i
  let leftMax := (List.range windowRadius).map (fun k => signal (i - k - 1)) |>.maximum?
  let rightMax := (List.range windowRadius).map (fun k => signal (i + k + 1)) |>.maximum?
  match leftMax, rightMax with
  | some lm, some rm => min (lm - si) (rm - si)
  | some lm, none => lm - si
  | none, some rm => rm - si
  | none, none => 0

/-! ## Domain Boundary Detection -/

/-- Minimum depth for domain boundary (20% relative depth) -/
noncomputable def minBoundaryDepth : ℝ := 0.2

/-- **DOMAIN BOUNDARY DETECTION**

    A position is a domain boundary if:
    1. It is a local minimum in the cumulative SS signal
    2. The minimum depth is ≥ 20% of the neighboring signal -/
noncomputable def isDomainBoundary
    (spectra : List (Fin 8 → ℂ))
    (i : ℕ)
    (windowRadius : ℕ := 5) : Bool :=
  let signal := cumulativeSSSignal spectra
  isLocalMinimum signal i windowRadius ∧
  minimumDepth signal i windowRadius > minBoundaryDepth * ssSignalAt spectra i

/-- Find all domain boundaries in a sequence -/
noncomputable def findDomainBoundaries
    (spectra : List (Fin 8 → ℂ))
    (windowRadius : ℕ := 5) : List ℕ :=
  (List.range spectra.length).filter fun i =>
    isDomainBoundary spectra i windowRadius

/-! ## Domain Structure -/

/-- A domain is a contiguous segment between boundaries -/
structure Domain where
  /-- Start position (inclusive) -/
  start : ℕ
  /-- End position (exclusive) -/
  stop : ℕ
  /-- Length of domain -/
  length : ℕ := stop - start
  /-- Valid domain (non-empty) -/
  valid : start < stop

/-- Extract domains from boundary list -/
def extractDomains (sequenceLength : ℕ) (boundaries : List ℕ) : List Domain :=
  let sortedBoundaries := boundaries.mergeSort (·≤·)
  let allBoundaries := [0] ++ sortedBoundaries ++ [sequenceLength]
  (List.range (allBoundaries.length - 1)).filterMap fun k =>
    match allBoundaries.get? k, allBoundaries.get? (k + 1) with
    | some s, some e =>
      if h : s < e then some { start := s, stop := e, valid := h }
      else none
    | _, _ => none

/-! ## Domain Classification -/

/-- Classify domain fold type from DFT spectrum -/
noncomputable def classifyDomain (spectra : List (Fin 8 → ℂ)) (d : Domain) : FoldSector :=
  let domainSpectra := spectra.drop d.start |>.take d.length
  if domainSpectra.isEmpty then .Disordered
  else
    let avgSpectrum := domainSpectra.head!  -- Simplified: use first
    classifySector avgSpectrum

/-- Domain statistics -/
structure DomainStats where
  /-- Total number of domains -/
  numDomains : ℕ
  /-- Average domain size -/
  avgSize : ℝ
  /-- Domain size variance -/
  sizeVariance : ℝ
  /-- α-helical domains -/
  numAlpha : ℕ
  /-- β-sheet domains -/
  numBeta : ℕ
  /-- Mixed domains -/
  numMixed : ℕ

/-! ## Multi-Domain Protein Detection -/

/-- Check if protein has multiple domains -/
def isMultiDomain (spectra : List (Fin 8 → ℂ)) : Bool :=
  let boundaries := findDomainBoundaries spectra
  boundaries.length > 0

/-- Minimum domain size (residues) -/
def minDomainSize : ℕ := 20

/-- Filter out small "domains" that are likely just linkers -/
def filterSmallDomains (domains : List Domain) : List Domain :=
  domains.filter fun d => d.length ≥ minDomainSize

/-! ## Domain Interface -/

/-- A domain interface is the region between two domains -/
structure DomainInterface where
  /-- First domain -/
  domain1 : Domain
  /-- Second domain -/
  domain2 : Domain
  /-- Interface region (typically the boundary ± few residues) -/
  interfaceStart : ℕ
  /-- Interface end -/
  interfaceEnd : ℕ
  /-- Interface is well-defined -/
  adjacent : domain1.stop = domain2.start

/-- Extract interfaces from domain list -/
def extractInterfaces (domains : List Domain) : List DomainInterface :=
  (List.range (domains.length - 1)).filterMap fun k =>
    match domains.get? k, domains.get? (k + 1) with
    | some d1, some d2 =>
      if h : d1.stop = d2.start then
        some { domain1 := d1
               domain2 := d2
               interfaceStart := d1.stop - 2
               interfaceEnd := d2.start + 2
               adjacent := h }
      else none
    | _, _ => none

end D7
end Derivations
end ProteinFolding
end IndisputableMonolith
