#!/usr/bin/env python3
"""
Technology Atlas Validation Script
Checks that all required files are present and properly formatted
"""

import os
import sys
from pathlib import Path
from typing import Dict, List, Tuple
import json

# Color codes for terminal output
class Colors:
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    BLUE = '\033[94m'
    BOLD = '\033[1m'
    END = '\033[0m'

# Required structure for each pillar
REQUIRED_STRUCTURE = {
    'README.md': 'Main pillar overview',
    'principles/core_principles.md': 'Recognition Science foundations',
    'theory/README.md': 'Mathematical foundations',
    'prototypes/README.md': 'Prototype specifications',
    'products/README.md': 'Commercial products roadmap',
    'research/open_questions.md': 'Active research questions',
    'references/papers.md': 'Reference papers and citations'
}

# Required root-level files
ROOT_FILES = {
    'README.md': 'Main repository navigation',
    'ROADMAP.md': 'Development timeline',
    'CROSS_PILLAR_INDEX.md': 'Integration mapping',
    'GLOSSARY.md': 'Recognition Science terminology',
    'CONTRIBUTING.md': 'Contribution guidelines',
    'PATENTS.md': 'IP tracking'
}

# Expected pillars
PILLARS = [
    '01-Anti-Gravity-Field-Propulsion',
    '02-Quantum-Hardware-Substrate-Computation',
    '03-AI-Training-Alignment-Consciousness',
    '04-Consciousness-Interfaces',
    '05-Ledger-Economics',
    '06-Energy-Generation',
    '07-Communication-Without-Carriers',
    '08-Metamaterials-Programmable-Matter',
    '09-Biomedical-Recognition-Engineering',
    '10-Sensing-Metrology',
    '11-Dual-Scale-Computation-Architecture',
    '12-Navigation-Autonomous-Timekeeping',
    '13-Climate-Planetary-Regulation',
    '14-Governance-Conflict-Resolution',
    '15-Reality-Editing'
]

def check_file_exists(filepath: Path) -> Tuple[bool, int]:
    """Check if file exists and return its line count"""
    if filepath.exists():
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                lines = len(f.readlines())
            return True, lines
        except:
            return True, 0
    return False, 0

def validate_pillar(pillar_path: Path) -> Dict[str, dict]:
    """Validate a single pillar directory"""
    results = {}
    
    for required_file, description in REQUIRED_STRUCTURE.items():
        file_path = pillar_path / required_file
        exists, lines = check_file_exists(file_path)
        results[required_file] = {
            'exists': exists,
            'lines': lines,
            'description': description
        }
    
    # Check for theory content beyond README
    theory_files = list((pillar_path / 'theory').glob('*.tex')) + \
                   list((pillar_path / 'theory').glob('*.lean')) + \
                   list((pillar_path / 'theory').glob('*.py'))
    
    results['theory_content'] = {
        'count': len(theory_files),
        'files': [f.name for f in theory_files]
    }
    
    return results

def print_pillar_report(pillar_name: str, results: Dict[str, dict]):
    """Print validation results for a pillar"""
    all_exist = all(r['exists'] for r in results.values() if isinstance(r, dict) and 'exists' in r)
    
    status_color = Colors.GREEN if all_exist else Colors.YELLOW
    status_symbol = '✓' if all_exist else '⚠'
    
    print(f"\n{status_color}{status_symbol} {pillar_name}{Colors.END}")
    
    for file_path, info in results.items():
        if file_path == 'theory_content':
            continue
            
        if info['exists']:
            print(f"  {Colors.GREEN}✓{Colors.END} {file_path} ({info['lines']} lines)")
        else:
            print(f"  {Colors.RED}✗{Colors.END} {file_path} - MISSING")
    
    # Theory content
    theory_info = results['theory_content']
    if theory_info['count'] > 0:
        print(f"  {Colors.BLUE}◆{Colors.END} Theory content: {theory_info['count']} files")
        for fname in theory_info['files'][:3]:  # Show first 3
            print(f"    - {fname}")
    else:
        print(f"  {Colors.YELLOW}○{Colors.END} No additional theory files yet")

def validate_root_files(root_path: Path) -> Dict[str, dict]:
    """Validate root-level files"""
    results = {}
    
    for required_file, description in ROOT_FILES.items():
        file_path = root_path / required_file
        exists, lines = check_file_exists(file_path)
        results[required_file] = {
            'exists': exists,
            'lines': lines,
            'description': description
        }
    
    return results

def generate_summary_report(all_results: Dict) -> Dict:
    """Generate summary statistics"""
    summary = {
        'total_files': 0,
        'missing_files': 0,
        'total_lines': 0,
        'pillars_complete': 0,
        'theory_files': 0
    }
    
    # Count pillar statistics
    for pillar, results in all_results['pillars'].items():
        pillar_complete = True
        for file_info in results.values():
            if isinstance(file_info, dict) and 'exists' in file_info:
                summary['total_files'] += 1
                if file_info['exists']:
                    summary['total_lines'] += file_info['lines']
                else:
                    summary['missing_files'] += 1
                    pillar_complete = False
        
        if pillar_complete:
            summary['pillars_complete'] += 1
        
        if 'theory_content' in results:
            summary['theory_files'] += results['theory_content']['count']
    
    # Count root files
    for file_info in all_results['root'].values():
        summary['total_files'] += 1
        if file_info['exists']:
            summary['total_lines'] += file_info['lines']
        else:
            summary['missing_files'] += 1
    
    return summary

def main():
    """Main validation routine"""
    print(f"{Colors.BOLD}Technology Atlas Validation Report{Colors.END}")
    print("=" * 50)
    
    # Determine root path
    script_dir = Path(__file__).parent
    root_path = script_dir.parent
    
    # Validate root files
    print(f"\n{Colors.BOLD}Root Files:{Colors.END}")
    root_results = validate_root_files(root_path)
    
    for file_name, info in root_results.items():
        if info['exists']:
            print(f"{Colors.GREEN}✓{Colors.END} {file_name} ({info['lines']} lines)")
        else:
            print(f"{Colors.RED}✗{Colors.END} {file_name} - MISSING")
    
    # Validate each pillar
    print(f"\n{Colors.BOLD}Pillar Validation:{Colors.END}")
    all_results = {'root': root_results, 'pillars': {}}
    
    for pillar in PILLARS:
        pillar_path = root_path / pillar
        if pillar_path.exists():
            results = validate_pillar(pillar_path)
            all_results['pillars'][pillar] = results
            print_pillar_report(pillar, results)
        else:
            print(f"\n{Colors.RED}✗ {pillar} - DIRECTORY MISSING{Colors.END}")
    
    # Generate summary
    print(f"\n{Colors.BOLD}Summary:{Colors.END}")
    print("=" * 50)
    
    summary = generate_summary_report(all_results)
    
    print(f"Total files checked: {summary['total_files']}")
    print(f"Missing files: {summary['missing_files']}")
    print(f"Total documentation lines: {summary['total_lines']:,}")
    print(f"Pillars complete: {summary['pillars_complete']}/15")
    print(f"Theory files created: {summary['theory_files']}")
    
    # Determine exit status
    if summary['missing_files'] == 0:
        print(f"\n{Colors.GREEN}{Colors.BOLD}✓ All validation checks passed!{Colors.END}")
        sys.exit(0)
    else:
        print(f"\n{Colors.YELLOW}{Colors.BOLD}⚠ Validation completed with {summary['missing_files']} missing files{Colors.END}")
        sys.exit(1)

if __name__ == "__main__":
    main() 