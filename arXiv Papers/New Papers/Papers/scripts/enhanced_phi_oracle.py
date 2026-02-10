#!/usr/bin/env python3
"""
Enhanced Phi Oracle for RSA Factorization
Based on Recognition Science eight-phase interference
"""

import math
import time
from typing import Dict, Optional, Tuple

# Golden ratio constant
PHI = (1 + math.sqrt(5)) / 2
C_STAR = PHI - 1.5  # The universal constant: 0.11803398874989...

def eight_phase_coherence(N: int, q: int) -> float:
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

def discrimination_score(N: int, q: int) -> float:
    """Calculate the discrimination score S(N,q)"""
    F = eight_phase_coherence(N, q)
    
    # Check if q divides N
    if N % q == 0:
        # For true factors: S = (1 - F) * (φ - 0.5)
        return (1 - F) * (PHI - 0.5)
    else:
        # For non-factors: S = 1 + |F| * exp(-φ/√N)
        return 1 + abs(F) * math.exp(-PHI / math.sqrt(N))

def get_k_candidates(N: int, max_candidates: int = 1000) -> list:
    """Generate candidate k values based on Fibonacci-like denominators"""
    candidates = []
    
    # Fibonacci-like denominators from the paper
    fibonacci_like = [1, 2, 3, 5, 8, 13, 21, 34, 55, 61]
    
    # Determine search range based on N's bit size
    bits = N.bit_length()
    k_range = min(bits // 10, 20)  # Adaptive range
    
    for d in fibonacci_like:
        for n in range(-k_range * d, k_range * d + 1):
            if d == 0:
                continue
            k = n / d
            # Calculate the corresponding q value
            q_approx = int(math.sqrt(N) * (PHI ** k))
            
            # Only include reasonable candidates
            if q_approx > 1 and q_approx < N:
                candidates.append((k, q_approx))
    
    # Sort by proximity to sqrt(N)
    sqrt_N = int(math.sqrt(N))
    candidates.sort(key=lambda x: abs(x[1] - sqrt_N))
    
    return candidates[:max_candidates]

def get_prediction_with_delta(N: int, max_time_ms: int = 5000) -> Dict:
    """
    Enhanced interface that returns best candidate with delta information
    """
    start_time = time.time()
    max_time_s = max_time_ms / 1000.0
    
    # Get candidate values
    candidates = get_k_candidates(N, max_candidates=10000)
    
    best_score = float('inf')
    best_candidate = None
    best_k = None
    candidates_tested = 0
    
    # Test candidates
    for k, q_approx in candidates:
        if time.time() - start_time > max_time_s:
            break
            
        candidates_tested += 1
        
        # Test exact candidate
        if N % q_approx == 0:
            # Found exact factor!
            return {
                'prediction': q_approx,
                'is_exact': True,
                'candidates_tested': candidates_tested,
                'k_value': k
            }
        
        # Calculate discrimination score
        score = discrimination_score(N, q_approx)
        
        # Track best candidate (closest to C_STAR for factors, lowest for non-factors)
        if abs(score - C_STAR) < abs(best_score - C_STAR):
            best_score = score
            best_candidate = q_approx
            best_k = k
        
        # Also test nearby values
        for delta in [-1, 1, -2, 2]:
            test_q = q_approx + delta
            if test_q > 1 and test_q < N:
                candidates_tested += 1
                
                if N % test_q == 0:
                    # Found exact factor!
                    return {
                        'prediction': test_q,
                        'is_exact': True,
                        'candidates_tested': candidates_tested,
                        'k_value': k
                    }
                
                score = discrimination_score(N, test_q)
                if abs(score - C_STAR) < abs(best_score - C_STAR):
                    best_score = score
                    best_candidate = test_q
                    best_k = k
    
    # Return best candidate found
    return {
        'prediction': best_candidate if best_candidate else int(math.sqrt(N)),
        'is_exact': False,
        'candidates_tested': candidates_tested,
        'best_score': best_score,
        'k_value': best_k
    }

def factor(N: int) -> Optional[Tuple[int, int]]:
    """
    Standard factoring interface for compatibility
    """
    result = get_prediction_with_delta(N, max_time_ms=30000)
    
    if result['is_exact']:
        p = result['prediction']
        q = N // p
        return (min(p, q), max(p, q))
    
    return None

def phi_perfect_factorize(N: int, verbose: bool = True) -> Optional[Tuple[int, int]]:
    """
    Compatibility interface that mimics the perfect factorization
    """
    if verbose:
        print(f"Attempting to factor N = {N} ({N.bit_length()} bits)")
    
    result = get_prediction_with_delta(N, max_time_ms=60000)
    
    if result['is_exact']:
        p = result['prediction']
        q = N // p
        if verbose:
            print(f"Success! Found factors: p = {p}, q = {q}")
        return (min(p, q), max(p, q))
    
    if verbose:
        print(f"Failed to find exact factors. Best candidate: {result['prediction']}")
    
    return None 