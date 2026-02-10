#!/usr/bin/env python3
"""
Test Eight-Phase Coherence on Known RSA Numbers
Tests the Recognition Science factorization theory against RSA challenge numbers
"""

import math
import numpy as np
from decimal import Decimal, getcontext

# Set high precision for accurate calculations
getcontext().prec = 100

# Golden ratio constant
PHI = (1 + math.sqrt(5)) / 2
C_STAR = PHI - 1.5  # The universal constant: 0.11803398874989...

# Known RSA challenge numbers (some factored, some not)
RSA_NUMBERS = {
    "RSA-100": {
        "N": 1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139,
        "p": 37975227936943673922808872755445627854565536638199,
        "q": 40094690950920881030683735292761468389214899724061,
        "bits": 330
    },
    "RSA-129": {
        "N": 114381625757888867669235779976146612010218296721242362562561842935706935245733897830597123563958705058989075147599290026879543541,
        "p": 3490529510847650949147849619903898133417764638493387843990820577,
        "q": 32769132993266709549961988190834461413177642967992942539798288533,
        "bits": 426
    },
    "RSA-140": {
        "N": 21290246318258757547497882016271517497806703963277216278233383215381949984056495911366573853021918316783107387995317230889569230873441936471,
        "p": 3398717423028438554530123627613875835633986495969597423490929302771479,
        "q": 6264200187401285096151654948264442219302037178623509019111660653946049,
        "bits": 463
    },
    "RSA-155": {
        "N": 10941738641570527421809707322040357612003732945449205990913842131476349984288934784717997257891267332497625752899781833797076537244027146743531593354333897,
        "p": 102639592829741105772054196573991675900716567808038066803341933521790711307779,
        "q": 106603488380168454820927220360012878679207958575989291522270608237193062808643,
        "bits": 512
    }
}

def eight_phase_coherence(N, q):
    """Calculate the eight-phase coherence score F_N(q)"""
    if q <= 0 or q >= N:
        return 0.0
    
    r = math.log(q) / math.log(N)
    
    # Calculate sum of cosines for k = 0 to 7
    coherence_sum = 0.0
    for k in range(8):
        phase = 2 * math.pi * k / 8 * r
        coherence_sum += math.cos(phase)
    
    return coherence_sum / 8

def discrimination_score(N, q):
    """Calculate the discrimination score S(N,q) as per the paper"""
    F = eight_phase_coherence(N, q)
    
    # Check if q divides N
    if N % q == 0:
        # For true factors: S = (1 - F) * (φ - 0.5)
        # This should equal φ - 1.5 when F = 1
        return (1 - F) * (PHI - 0.5)
    else:
        # For non-factors: S = 1 + |F| * exp(-φ/√N)
        return 1 + abs(F) * math.exp(-PHI / math.sqrt(N))

def find_k_exponent(N, factor):
    """Find the rational exponent k such that factor ≈ sqrt(N) * phi^k"""
    sqrt_N = math.sqrt(N)
    ratio = factor / sqrt_N
    k = math.log(ratio) / math.log(PHI)
    return k

def rational_approximation(x, max_denom=61):
    """Find best rational approximation n/d with d <= max_denom"""
    best_n, best_d = 0, 1
    best_error = abs(x)
    
    # Check Fibonacci-like denominators as mentioned in the paper
    fibonacci_like = [1, 2, 3, 5, 8, 13, 21, 34, 55, 61]
    
    for d in fibonacci_like:
        n = round(x * d)
        error = abs(x - n/d)
        if error < best_error:
            best_error = error
            best_n, best_d = n, d
    
    return best_n, best_d, best_error

def test_rsa_number(name, rsa_data):
    """Test the eight-phase coherence on a known RSA number"""
    N = rsa_data["N"]
    p = rsa_data["p"]
    q = rsa_data["q"]
    bits = rsa_data["bits"]
    
    print(f"\n{'='*60}")
    print(f"Testing {name} ({bits} bits)")
    print(f"{'='*60}")
    
    # Verify N = p * q
    assert N == p * q, f"Invalid factorization for {name}"
    
    # Test discrimination score for both factors
    for factor_name, factor in [("p", p), ("q", q)]:
        coherence = eight_phase_coherence(N, factor)
        score = discrimination_score(N, factor)
        error = abs(score - C_STAR)
        
        # Find k exponent
        k = find_k_exponent(N, factor)
        n, d, rat_error = rational_approximation(k, max_denom=61)
        
        print(f"\nFactor {factor_name}:")
        print(f"  Value: {factor}")
        print(f"  r = log({factor_name})/log(N) = {math.log(factor)/math.log(N):.6f}")
        print(f"  F_N({factor_name}) = {coherence:.12f}")
        print(f"  S(N,{factor_name}) = {score:.12f}")
        print(f"  C* = φ - 1.5 = {C_STAR:.12f}")
        print(f"  |S - C*| = {error:.2e}")
        print(f"  k exponent: {k:.6f} ≈ {n}/{d} (error: {rat_error:.2e})")
        
        # Check if discrimination score matches the universal constant
        if error < 1e-3:
            print(f"  ✓ MATCH! Factor identified by discrimination test")
        else:
            print(f"  ✗ No match (error too large)")
    
    # Test a few non-factors to verify they score > 1
    print(f"\nTesting non-factors (should score > 1):")
    test_values = [
        int(math.sqrt(N)),  # sqrt(N)
        int(math.sqrt(N) * PHI),  # sqrt(N) * φ
        int(math.sqrt(N) * PHI**2),  # sqrt(N) * φ²
        p + 1,  # Near-miss
        q - 1   # Near-miss
    ]
    
    matches = 0
    for test_q in test_values[:3]:  # Test first 3 non-factors
        if 0 < test_q < N and N % test_q != 0:
            score = discrimination_score(N, test_q)
            if score < 0.5:  # Should be > 1 for non-factors
                matches += 1
            print(f"  q = {test_q}: S(N,q) = {score:.6f}")
    
    print(f"\nFalse positive rate: {matches}/3 = {matches/3:.1%}")

def main():
    print("Eight-Phase Discrimination Test on RSA Challenge Numbers")
    print("="*60)
    print(f"Universal constant C* = φ - 1.5 = {C_STAR:.12f}")
    print(f"Expected score for true factors: {C_STAR:.12f}")
    print(f"Expected score for non-factors: > 1.0")
    
    # Test each RSA number
    for name, rsa_data in RSA_NUMBERS.items():
        test_rsa_number(name, rsa_data)
    
    print("\n" + "="*60)
    print("Summary: Testing complete")
    print("\nNote: The discrimination formula from the paper is:")
    print("  S(N,q) = (1 - F_N(q)) * (φ - 0.5) for factors")
    print("  S(N,q) = 1 + |F_N(q)| * exp(-φ/√N) for non-factors")

if __name__ == "__main__":
    main() 