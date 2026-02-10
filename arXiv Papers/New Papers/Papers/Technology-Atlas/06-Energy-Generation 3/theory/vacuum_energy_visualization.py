#!/usr/bin/env python3
"""
Vacuum Energy Extraction Visualization
Shows how recognition pairs in vacuum can be separated for energy extraction
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from matplotlib.patches import Circle, FancyBboxPatch
import matplotlib.patches as mpatches

# Recognition Science constants
PHI = (1 + np.sqrt(5)) / 2
E_COH = 0.090  # eV
HBAR_C = 197.3  # eV·nm
LAMBDA_IR = HBAR_C / E_COH  # 13.8 μm

class VacuumRecognitionPair:
    """Represents a balanced recognition pair in vacuum"""
    
    def __init__(self, position, phase=0):
        self.position = np.array(position)
        self.phase = phase
        self.separated = False
        self.energy = 0
        
    def update(self, field_strength, dt):
        """Update pair state under recognition field"""
        if not self.separated and field_strength > 0.5:
            # Field strong enough to separate pair
            self.separated = True
            self.energy = 2 * E_COH  # Energy extracted
        
        # Phase evolution
        self.phase += 2 * np.pi * dt / 8  # Eight-beat cycle
        
    def draw(self, ax, time):
        """Visualize the recognition pair"""
        x, y = self.position
        
        if not self.separated:
            # Balanced pair - overlapping circles
            plus = Circle((x-0.1, y), 0.3, color='red', alpha=0.5)
            minus = Circle((x+0.1, y), 0.3, color='blue', alpha=0.5)
            ax.add_patch(plus)
            ax.add_patch(minus)
            ax.text(x, y, '0', ha='center', va='center', fontsize=12, 
                   fontweight='bold')
        else:
            # Separated pair - energy available
            separation = 0.5 + 0.2 * np.sin(self.phase)
            plus = Circle((x-separation, y), 0.3, color='red', alpha=0.7)
            minus = Circle((x+separation, y), 0.3, color='blue', alpha=0.7)
            ax.add_patch(plus)
            ax.add_patch(minus)
            
            # Energy indication
            ax.text(x, y+0.8, f'+{self.energy:.3f} eV', 
                   ha='center', va='center', fontsize=10, color='green')

def create_vacuum_field_visualization():
    """Create static visualization of vacuum recognition field"""
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    # Left panel: Vacuum structure
    ax1.set_title('Vacuum = Balanced Recognition Pairs', fontsize=14)
    ax1.set_xlim(-2, 2)
    ax1.set_ylim(-2, 2)
    ax1.set_aspect('equal')
    
    # Create grid of balanced pairs
    for i in range(5):
        for j in range(5):
            x = -1.5 + i * 0.75
            y = -1.5 + j * 0.75
            plus = Circle((x-0.05, y), 0.15, color='red', alpha=0.3)
            minus = Circle((x+0.05, y), 0.15, color='blue', alpha=0.3)
            ax1.add_patch(plus)
            ax1.add_patch(minus)
    
    ax1.text(0, -2.5, r'$|0\rangle = \sum_k \alpha_k |+k\rangle|-k\rangle$', 
             ha='center', fontsize=12)
    ax1.set_xlabel('Space is dormant light in balance')
    ax1.grid(True, alpha=0.2)
    ax1.set_xticks([])
    ax1.set_yticks([])
    
    # Right panel: Energy extraction mechanism
    ax2.set_title('φ-Resonant Energy Extraction', fontsize=14)
    ax2.set_xlim(0, 10)
    ax2.set_ylim(0, 5)
    
    # Time axis
    t = np.linspace(0, 10, 1000)
    
    # Recognition field (golden ratio frequency)
    field = np.sin(2 * np.pi * t / PHI)
    ax2.plot(t, 2.5 + field, 'g-', linewidth=2, label='Recognition Field')
    
    # Energy extraction events
    extraction_times = [2.5, 5.0, 7.5]
    for te in extraction_times:
        ax2.axvline(x=te, color='red', linestyle='--', alpha=0.5)
        ax2.text(te, 4.5, 'Extract', rotation=90, va='bottom', ha='right')
    
    # Efficiency curve
    efficiency = 1 - np.exp(-t/3)
    ax2.plot(t, efficiency, 'b-', linewidth=2, label='Extraction Efficiency')
    
    ax2.set_xlabel('Time (units of τ₀)')
    ax2.set_ylabel('Normalized Units')
    ax2.legend()
    ax2.grid(True, alpha=0.2)
    
    plt.tight_layout()
    return fig

def create_resonance_diagram():
    """Create diagram showing φ-resonance coupling"""
    
    fig, ax = plt.subplots(figsize=(10, 8))
    
    # Frequency spectrum
    frequencies = np.logspace(-2, 2, 1000)
    
    # Resonance peaks at φⁿ
    response = np.zeros_like(frequencies)
    for n in range(-5, 6):
        f_res = PHI**n
        width = 0.1 * f_res
        response += 1 / (1 + ((frequencies - f_res) / width)**2)
    
    ax.loglog(frequencies, response, 'b-', linewidth=2)
    
    # Mark golden ratio harmonics
    for n in range(-3, 4):
        f = PHI**n
        if 0.01 < f < 100:
            ax.axvline(x=f, color='red', linestyle='--', alpha=0.5)
            ax.text(f, 1e-3, f'φ^{n}', rotation=90, va='bottom', ha='right')
    
    # Annotations
    ax.set_xlabel('Frequency (units of fundamental)', fontsize=12)
    ax.set_ylabel('Vacuum Response', fontsize=12)
    ax.set_title('Golden Ratio Resonances in Vacuum Energy Extraction', fontsize=14)
    ax.grid(True, alpha=0.3, which='both')
    
    # Add efficiency annotation
    ax.text(1, 0.3, 'Peak efficiency at\nφ-harmonic frequencies', 
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8),
            fontsize=10, ha='center')
    
    return fig

def simulate_vacuum_tap():
    """Simulate vacuum tap energy extraction"""
    
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8))
    
    # Simulation parameters
    time_steps = 1000
    dt = 0.01
    field_frequency = 1 / PHI  # Golden ratio frequency
    
    # Initialize vacuum pairs
    n_pairs = 20
    pairs = []
    for i in range(n_pairs):
        x = -4 + (i % 5) * 2
        y = -2 + (i // 5) * 1.5
        pairs.append(VacuumRecognitionPair([x, y], phase=i*0.1))
    
    # Storage for results
    time = []
    total_energy = []
    field_strength_history = []
    
    # Animation function
    def animate(frame):
        ax1.clear()
        ax2.clear()
        
        t = frame * dt
        field_strength = 0.5 * (1 + np.sin(2 * np.pi * field_frequency * t))
        
        # Update pairs
        energy_sum = 0
        for pair in pairs:
            pair.update(field_strength, dt)
            pair.draw(ax1, t)
            energy_sum += pair.energy
        
        # Store data
        time.append(t)
        total_energy.append(energy_sum)
        field_strength_history.append(field_strength)
        
        # Top panel: Vacuum state
        ax1.set_xlim(-5, 5)
        ax1.set_ylim(-3, 3)
        ax1.set_title(f'Vacuum Recognition Pairs (t = {t:.2f})', fontsize=14)
        ax1.set_aspect('equal')
        
        # Add field indicator
        field_box = FancyBboxPatch((-5, -3), 10, 0.3, 
                                  boxstyle="round,pad=0.1",
                                  facecolor='green', 
                                  alpha=field_strength)
        ax1.add_patch(field_box)
        ax1.text(0, -2.7, f'Field Strength: {field_strength:.2f}', 
                ha='center', fontsize=10)
        
        # Bottom panel: Energy extraction
        ax2.plot(time, total_energy, 'b-', linewidth=2, label='Extracted Energy')
        ax2.plot(time, np.array(field_strength_history) * max(total_energy) if total_energy else [0], 
                'g--', alpha=0.5, label='Field Strength (scaled)')
        
        ax2.set_xlabel('Time')
        ax2.set_ylabel('Energy (eV)')
        ax2.set_title('Cumulative Energy Extraction')
        ax2.legend()
        ax2.grid(True, alpha=0.3)
        
        if time:
            ax2.set_xlim(0, max(time))
    
    # Create animation
    anim = FuncAnimation(fig, animate, frames=time_steps, interval=50, repeat=True)
    
    plt.tight_layout()
    return fig, anim

def create_power_scaling_plot():
    """Show power output scaling with system parameters"""
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    
    # Left: Power vs number of voxels
    n_voxels = np.logspace(3, 12, 100)
    power = n_voxels * E_COH * PHI**5 * 1e-6  # MW
    
    ax1.loglog(n_voxels, power, 'b-', linewidth=2)
    ax1.set_xlabel('Number of Voxels', fontsize=12)
    ax1.set_ylabel('Power Output (MW)', fontsize=12)
    ax1.set_title('Power Scaling with System Size', fontsize=14)
    ax1.grid(True, alpha=0.3, which='both')
    
    # Mark key points
    targets = [(1e6, '1 cm³'), (1e9, '1 m³'), (1e12, '1 km³')]
    for n, label in targets:
        p = n * E_COH * PHI**5 * 1e-6
        ax1.plot(n, p, 'ro', markersize=8)
        ax1.text(n, p*1.5, label, ha='center', fontsize=10)
    
    # Right: Efficiency vs resonance order
    n_order = np.arange(-5, 6)
    efficiency = 1 / (1 + 0.1 * n_order**2)
    
    ax2.bar(n_order, efficiency, color='green', alpha=0.7)
    ax2.set_xlabel('Resonance Order (n in φⁿ)', fontsize=12)
    ax2.set_ylabel('Extraction Efficiency', fontsize=12)
    ax2.set_title('Efficiency at Different φ-Harmonics', fontsize=14)
    ax2.grid(True, alpha=0.3, axis='y')
    
    # Highlight optimal range
    ax2.axvspan(-2, 2, alpha=0.2, color='yellow', label='Optimal Range')
    ax2.legend()
    
    plt.tight_layout()
    return fig

if __name__ == "__main__":
    # Create all visualizations
    print("Generating vacuum energy visualizations...")
    
    # 1. Vacuum structure
    fig1 = create_vacuum_field_visualization()
    fig1.savefig('vacuum_structure.png', dpi=150, bbox_inches='tight')
    print("Saved: vacuum_structure.png")
    
    # 2. Resonance diagram  
    fig2 = create_resonance_diagram()
    fig2.savefig('phi_resonances.png', dpi=150, bbox_inches='tight')
    print("Saved: phi_resonances.png")
    
    # 3. Power scaling
    fig3 = create_power_scaling_plot()
    fig3.savefig('power_scaling.png', dpi=150, bbox_inches='tight')
    print("Saved: power_scaling.png")
    
    # 4. Animated simulation (save first frame)
    fig4, anim = simulate_vacuum_tap()
    fig4.savefig('vacuum_tap_simulation.png', dpi=150, bbox_inches='tight')
    print("Saved: vacuum_tap_simulation.png")
    
    # Note: To save animation as video:
    # anim.save('vacuum_tap.mp4', writer='ffmpeg', fps=20)
    
    print("\nKey insights visualized:")
    print("1. Vacuum consists of balanced recognition pairs")
    print("2. φ-resonant fields can separate pairs for energy")
    print("3. Power scales with voxel count and resonance order")
    print("4. Continuous extraction possible with proper tuning") 