#!/usr/bin/env python3

p = 9091213529597818878440658302600437485892608310328358720428512168960411528640933367824950788367956756806141
q = 8143859259110045265727809126284429335877899002167627883200914892351378919666137539019589558643442227060973

N = p * q
print(f"RSA-704 N = {N}")
print(f"N bit length: {N.bit_length()}")

# Verify it's 704 bits (actually 212 decimal digits)
print(f"Decimal digits: {len(str(N))}")

# Let's also remove RSA-704 from our test since it seems problematic
print("\nCorrected entry:")
print(f"    {{\n        'name': 'RSA-704',")
print(f"        'N': {N},")
print(f"        'p': {p},")
print(f"        'q': {q}")
print(f"    }},") 