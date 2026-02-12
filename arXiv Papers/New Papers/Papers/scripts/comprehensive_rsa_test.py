#!/usr/bin/env python3
"""
Comprehensive RSA Delta Test
Tests all known RSA pairs and measures delta between predicted and
actual factors
"""

import numpy as np
from rsa_known_pairs import RSA_PAIRS
import importlib
import sys
import time
import random

def verify_rsa_pair(N, p, q):
    """Verify that p * q = N and both are prime"""
    if p * q != N:
        return False, f"Product mismatch: {p} * {q} = {p*q} != {N}"
    
    # Simple primality check using Python's built-in
    def is_probable_prime(n, k=5):
        if n < 2:
            return False
        if n == 2 or n == 3:
            return True
        if n % 2 == 0:
            return False
        
        # Miller-Rabin test
        r, d = 0, n - 1
        while d % 2 == 0:
            r += 1
            d //= 2
        
        for _ in range(k):
            # Use Python's random for large numbers
            import random
            a = random.randint(2, n - 2)
            x = pow(a, d, n)
            if x == 1 or x == n - 1:
                continue
            for _ in range(r - 1):
                x = pow(x, 2, n)
                if x == n - 1:
                    break
            else:
                return False
        return True
    
    if not is_probable_prime(p):
        return False, f"p={p} is not prime"
    if not is_probable_prime(q):
        return False, f"q={q} is not prime"
    
    return True, "Valid"

def test_oracle_with_deltas(oracle_module, oracle_name, max_time_ms=5000):
    """Test an oracle against all RSA pairs, always computing deltas"""
    print(f"\n{'='*80}")
    print(f"Testing {oracle_name}")
    print(f"{'='*80}\n")
    
    # First verify all RSA pairs
    print("Verifying RSA pairs...")
    all_valid = True
    for pair in RSA_PAIRS:
        valid, msg = verify_rsa_pair(pair['N'], pair['p'], pair['q'])
        if not valid:
            print(f"❌ {pair['name']}: {msg}")
            all_valid = False
        else:
            print(f"✓ {pair['name']}: Verified")
    
    if not all_valid:
        print("\nError: Some RSA pairs are invalid!")
        return None
    
    print(f"\nAll {len(RSA_PAIRS)} RSA pairs verified successfully!\n")
    
    # Test oracle predictions
    results = []
    print("Testing oracle predictions...\n")
    
    for pair in RSA_PAIRS:
        N = pair['N']
        actual_p = min(pair['p'], pair['q'])
        actual_q = max(pair['p'], pair['q'])
        
        print(f"Testing {pair['name']} (N={N}, {N.bit_length()} bits)...")
        
        try:
            start_time = time.time()
            
            # Try to get prediction with delta info
            if hasattr(oracle_module, 'get_prediction_with_delta'):
                # Use the enhanced interface
                pred_info = oracle_module.get_prediction_with_delta(N, max_time_ms=max_time_ms)
                elapsed = time.time() - start_time
                
                pred_candidate = pred_info['prediction']
                is_exact = pred_info['is_exact']
                candidates_tested = pred_info.get('candidates_tested', 0)
                
                if is_exact and N % pred_candidate == 0:
                    # Exact factor found
                    pred_p = pred_candidate
                    pred_q = N // pred_candidate
                    if pred_p > pred_q:
                        pred_p, pred_q = pred_q, pred_p
                    
                    delta_p = abs(pred_p - actual_p) / actual_p * 100
                    delta_q = abs(pred_q - actual_q) / actual_q * 100
                    avg_delta = (delta_p + delta_q) / 2
                    
                    print(f"  ✓ Found exact factors! (tested {candidates_tested} candidates in {elapsed:.2f}s)")
                    print(f"    Predicted: p={pred_p}, q={pred_q}")
                    print(f"    Actual:    p={actual_p}, q={actual_q}")
                    print(f"    Average delta: {avg_delta:.6f}%")
                    
                    results.append({
                        'name': pair['name'],
                        'N': N,
                        'N_bits': N.bit_length(),
                        'success': True,
                        'exact': True,
                        'pred_p': pred_p,
                        'pred_q': pred_q,
                        'actual_p': actual_p,
                        'actual_q': actual_q,
                        'delta_p': delta_p,
                        'delta_q': delta_q,
                        'avg_delta': avg_delta,
                        'candidates_tested': candidates_tested,
                        'time': elapsed
                    })
                else:
                    # No exact factor, but we have a best candidate
                    delta_from_p = abs(pred_candidate - actual_p) / actual_p * 100
                    delta_from_q = abs(pred_candidate - actual_q) / actual_q * 100
                    
                    # Use the smaller delta (candidate is closer to one of the factors)
                    best_delta = min(delta_from_p, delta_from_q)
                    
                    print(f"  ⚠️  Best candidate: {pred_candidate} (tested {candidates_tested} in {elapsed:.2f}s)")
                    print(f"    Delta from p: {delta_from_p:.3f}%")
                    print(f"    Delta from q: {delta_from_q:.3f}%")
                    print(f"    Best delta: {best_delta:.3f}%")
                    
                    results.append({
                        'name': pair['name'],
                        'N': N,
                        'N_bits': N.bit_length(),
                        'success': True,
                        'exact': False,
                        'best_candidate': pred_candidate,
                        'actual_p': actual_p,
                        'actual_q': actual_q,
                        'best_delta': best_delta,
                        'candidates_tested': candidates_tested,
                        'time': elapsed
                    })
                    
            else:
                # Fallback for oracles without the enhanced interface
                # Try the standard factor method
                if hasattr(oracle_module, 'factor'):
                    result = oracle_module.factor(N)
                elif hasattr(oracle_module, 'factor_semiprime'):
                    result = oracle_module.factor_semiprime(N)
                elif hasattr(oracle_module, 'phi_perfect_factorize'):
                    result = oracle_module.phi_perfect_factorize(N, verbose=False)
                else:
                    print(f"  ❌ Oracle module has no compatible factoring method")
                    continue
                
                elapsed = time.time() - start_time
                
                if result is None:
                    print(f"  ❌ No factors found (took {elapsed:.2f}s)")
                    results.append({
                        'name': pair['name'],
                        'N': N,
                        'N_bits': N.bit_length(),
                        'success': False,
                        'time': elapsed
                    })
                    continue
                
                # Extract predicted factors
                if isinstance(result, tuple):
                    pred_p, pred_q = result
                elif isinstance(result, dict):
                    pred_p = result.get('p', result.get('factor1'))
                    pred_q = result.get('q', result.get('factor2'))
                else:
                    print(f"  ❌ Unexpected result format: {type(result)}")
                    continue
                
                # Ensure p < q for comparison
                if pred_p > pred_q:
                    pred_p, pred_q = pred_q, pred_p
                
                # Check if factorization is correct
                if pred_p * pred_q == N:
                    # Calculate deltas
                    delta_p = abs(pred_p - actual_p) / actual_p * 100
                    delta_q = abs(pred_q - actual_q) / actual_q * 100
                    avg_delta = (delta_p + delta_q) / 2
                    
                    print(f"  ✓ Success! (took {elapsed:.2f}s)")
                    print(f"    Predicted: p={pred_p}, q={pred_q}")
                    print(f"    Actual:    p={actual_p}, q={actual_q}")
                    print(f"    Average delta: {avg_delta:.6f}%")
                    
                    results.append({
                        'name': pair['name'],
                        'N': N,
                        'N_bits': N.bit_length(),
                        'success': True,
                        'exact': pred_p == actual_p and pred_q == actual_q,
                        'pred_p': pred_p,
                        'pred_q': pred_q,
                        'actual_p': actual_p,
                        'actual_q': actual_q,
                        'delta_p': delta_p,
                        'delta_q': delta_q,
                        'avg_delta': avg_delta,
                        'time': elapsed
                    })
                else:
                    print(f"  ❌ Incorrect factorization: {pred_p} * {pred_q} = {pred_p * pred_q} != {N}")
                    results.append({
                        'name': pair['name'],
                        'N': N,
                        'N_bits': N.bit_length(),
                        'success': False,
                        'time': elapsed
                    })
                    
        except Exception as e:
            print(f"  ❌ Error: {str(e)}")
            results.append({
                'name': pair['name'],
                'N': N,
                'N_bits': N.bit_length(),
                'success': False,
                'error': str(e)
            })
    
    # Summary statistics
    print(f"\n{'='*80}")
    print("SUMMARY STATISTICS")
    print(f"{'='*80}\n")
    
    successful = [r for r in results if r.get('success', False)]
    exact_matches = [r for r in successful if r.get('exact', False)]
    approximate = [r for r in successful if not r.get('exact', False)]
    failed = [r for r in results if not r.get('success', False)]
    
    print(f"Total tests: {len(results)}")
    print(f"Successful: {len(successful)} ({len(successful)/len(results)*100:.1f}%)")
    print(f"  - Exact factors: {len(exact_matches)}")
    print(f"  - Approximate: {len(approximate)}")
    print(f"Failed: {len(failed)} ({len(failed)/len(results)*100:.1f}%)")
    
    if exact_matches:
        avg_deltas = [r['avg_delta'] for r in exact_matches]
        print(f"\nFor exact factorizations:")
        print(f"  Average delta: {np.mean(avg_deltas):.6f}%")
        print(f"  Median delta:  {np.median(avg_deltas):.6f}%")
        print(f"  Min delta:     {np.min(avg_deltas):.6f}%")
        print(f"  Max delta:     {np.max(avg_deltas):.6f}%")
    
    if approximate:
        best_deltas = [r['best_delta'] for r in approximate]
        print(f"\nFor approximate predictions:")
        print(f"  Average best delta: {np.mean(best_deltas):.3f}%")
        print(f"  Median best delta:  {np.median(best_deltas):.3f}%")
        print(f"  Min best delta:     {np.min(best_deltas):.3f}%")
        print(f"  Max best delta:     {np.max(best_deltas):.3f}%")
    
    # Show performance by RSA size
    if successful:
        print(f"\nPerformance by RSA size:")
        for r in sorted(successful, key=lambda x: x['N_bits']):
            if r.get('exact'):
                print(f"  {r['name']} ({r['N_bits']} bits): EXACT (δ={r['avg_delta']:.6f}%) in {r['time']:.2f}s")
            else:
                print(f"  {r['name']} ({r['N_bits']} bits): APPROX (best δ={r['best_delta']:.3f}%) in {r['time']:.2f}s")
    
    if failed:
        print(f"\nFailed factorizations:")
        for r in failed:
            error_msg = r.get('error', 'No factors found')
            print(f"  {r['name']}: {error_msg}")
    
    return results

def main():
    # Test the enhanced phi oracle
    print("Testing Enhanced Phi Oracle with Delta Tracking")
    print("=" * 80)
    
    try:
        oracle_module = importlib.import_module('enhanced_phi_oracle')
        results = test_oracle_with_deltas(oracle_module, 'Enhanced Phi Oracle (Adaptive Bands)')
        
        # Additional analysis
        if results:
            successful = [r for r in results if r.get('success', False)]
            if successful:
                print(f"\n{'='*80}")
                print("DETAILED ANALYSIS")
                print(f"{'='*80}\n")
                
                # Group by bit size ranges
                ranges = [(0, 50), (50, 100), (100, 200), (200, 400), (400, 1000)]
                for low, high in ranges:
                    in_range = [r for r in successful if low <= r['N_bits'] < high]
                    if in_range:
                        exact = [r for r in in_range if r.get('exact')]
                        approx = [r for r in in_range if not r.get('exact')]
                        
                        print(f"\n{low}-{high} bit range:")
                        print(f"  Total: {len(in_range)}")
                        print(f"  Exact: {len(exact)}")
                        print(f"  Approximate: {len(approx)}")
                        
                        if approx:
                            avg_delta = np.mean([r['best_delta'] for r in approx])
                            print(f"  Average delta for approximations: {avg_delta:.3f}%")
                            
    except ImportError:
        print("❌ Could not import enhanced_phi_oracle")
    except Exception as e:
        print(f"❌ Error testing Enhanced Phi Oracle: {str(e)}")

if __name__ == "__main__":
    main() 