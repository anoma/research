import sage.all
from sage.rings.integer_ring import Z as ZZ
from ipa import *

# Pallas curve
p = ZZ(0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001)
assert p.is_prime()
r = ZZ(0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001)
assert r.is_prime()

# previous (BN446?) curve 
# p = ZZ(0x24000000000024000130e0000d7f70e4a803ca76f439266f443f9a5c7a8a6c7be4a775fe8e177fd69ca7e85d60050af41ffffcd300000001)
# assert p.is_prime()
# r = ZZ(0x24000000000024000130e0000d7f70e4a803ca76f439266f443f9a5cda8a6c7be4a7a5fe8fadffd6a2a7e8c30006b9459ffffcd300000001)
# assert r.is_prime()

Fp = GF(p)
Fr = GF(r)
# b for the previous (BN446?) curve
# b = Fp(57)
b = Fp(5)
E = EllipticCurve([Fp(0), b])
while E.order() % r != 0:
    b+=1
    E = EllipticCurve([Fp(0), b])

k = 6

# Test of the polynomial commitment scheme
H2C = IPACommitment(r, p, E, k)
pol = H2C.FrX([Fr.random_element() for i in range(1<<k)])
rand = Fr.random_element()

print('Commitment scheme')
ttt = cputime()
H2C.create(pol, rand)
ttt = cputime(ttt)
print('Commitment: {:5.3f}s'.format(ttt))
x = H2C.Fr.random_element()
ttt = cputime()
H2C.open(pol, x, rand)
print('Opening: {:5.3f}s'.format(ttt))

ttt = cputime()
assert H2C.verify(x)
print('Verification: {:5.3f}s.'.format(ttt))
