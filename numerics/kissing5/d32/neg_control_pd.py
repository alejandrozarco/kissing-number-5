"""Negative controls for round_hp.pd_certificate: a certificate's Gram block B, then B - c I for c just above and just
below its smallest eigenvalue (estimated with hp_blocks' inverse iteration); the certificate must fail for the first
(indefinite) and pass for the second."""
import json, sys, math, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from round_hp import pd_certificate
from hp_blocks import ldl_fixed, lam_min
J = json.load(open(sys.argv[1])); r = int(sys.argv[2]) if len(sys.argv) > 2 else 0
B = [[Fr(x) for x in row] for row in J["SOS"][r]["B"]]
L = 1
for row in B:
    for x in row: L = math.lcm(L, x.denominator)
Bn = [[x.numerator * (L // x.denominator) for x in row] for row in B]
P = 320
A = np.array([[(x << P) // L for x in row] for row in Bn], dtype=object)
Lf, d, bad = ldl_fixed(A, P); lam = lam_min(Lf, d, P, iters=60)
print(f"block {J['SOS'][r]['g']} size {len(B)}: lambda_min ~ {lam:.4e}")
for fac, expect in ((1.01, False), (0.99, True)):
    c = Fr(lam * fac)
    Bc = [[Bn[i][j] - (c.numerator * L // c.denominator if i == j else 0) for j in range(len(B))] for i in range(len(B))]
    # B - c I with c rational: scale exactly
    Bc = [[Bn[i][j] * c.denominator - (c.numerator * L if i == j else 0) for j in range(len(B))] for i in range(len(B))]
    ok, info = pd_certificate(Bc, L * c.denominator, P)
    print(f"  B - {fac} lambda_min I: certificate {'PASS' if ok else 'FAIL'} ({info}); expected {'PASS' if expect else 'FAIL'}"
          f" -> {'OK' if ok == expect else 'WRONG'}")
