# -*- coding: utf-8 -*-
import hashlib
from random import randint
import sage.all
from sage.arith.misc import is_prime
from sage.rings.finite_rings.finite_field_constructor import FiniteField as GF
from sage.schemes.elliptic_curves.constructor import EllipticCurve
from sage.rings.integer_ring import Z as ZZ
from sage.misc.functional import cyclotomic_polynomial
from sage.matrix.constructor import Matrix
from sage.misc.misc import cputime

'''
IPA proof scheme

Notation: The curve is defined over Fp, with a subrgoup of order r.
'''

class IPACommitment():
    def __init__(self, r, p, E, k):
        self.r = r
        self.Fr = GF(r)
        self.FrX = self.Fr['X']
        self.p = p
        self.Fp = GF(p)
        self.FpY = self.Fp['Y']
        self.E = E
        if p.nbits() == 255: # Pallas curve
            self.Egen = E([8846324870586583739111697172863888851520659981074829056268361825029048600336,26279573376377669217484965006105184765343200454744742625721925061231198562202])
        elif p.nbits() == 446: #BN446 curve
            self.Egen = E([49205752480027619249597164880830948877279512374686345868875722799161419753941861232388656204725841432352919280728771423940349892387127, 16418904400463023154191453557729732347625441881882091737443892890253596882544459457792155542560493982175671266780907192157775959777313])
        else:
            assert False
        self.k = k
        self.d = 1<<k
        self.G_bold = [E.random_point() for i in range(self.d)]
        self.H = E.random_point()
        self.value = E(0)
        self.opening = []

    def inner_product(self, L1, L2):
        # L1 corresponds to scalars
        while len(L1)  < len(L2) :
            L1 += [0]
        assert len(L1) == len(L2)
        res = 0
        for i in range(len(L1)) :
            res += ZZ(L1[i]) * L2[i]
        return res

    def rho(self, *arg):
        return int(hashlib.sha256((str(arg)).encode()).hexdigest(),16)
    
    def create(self, polynomial, rand):
        # `polynomial` is an element of Fr[X] of degree \leq d
        # `rand` is a random element of Fr.
        #
        # return \sum p_i G_i + rand * H
        pol_list = polynomial.list()
        while len(pol_list) < len(self.G_bold):
            pol_list += [0]
        self.value = self.inner_product(pol_list + [rand], self.G_bold + [self.H])

    def open(self, polynomial, x, rand):
        # `polynomial` is an elemnt of Fr[X] of degree \leq d
        # x an element of Fr, where `polynomial` is evaluated at
        #
        # compute a proof pi of the evaluation of `polynomial` at `x`.
        
        # polynomial that is 0 at x
        s = self.FrX([self.Fr.random_element() for i in range(self.d)])
        v_prime = s(x)
        s -= v_prime
        assert s(x) == 0
    
        # commitment for s
        s_b = self.Fr.random_element()
        C_s = self.inner_product(s.list() + [s_b], self.G_bold + [self.H])
        
        # challenges
        iota = self.Fr(self.rho(C_s))
        z = self.Fr(self.rho(iota))

        final_poly = s * iota + polynomial
        v = final_poly(x)
        final_poly -= v
        blind = s_b*iota + rand
    
        a = final_poly.list()
        while len(a) < self.d :
            a = a + [0]
        aa = a
        b = [1]
        for i in range(1, self.d):
            b.append(b[-1] * x)
        bb = b
        G = self.G_bold
        H = self.H
        L = []
        R = []
        rand_l = []
        rand_r = []

        U = ZZ(self.Fr(self.rho(x))) * self.Egen

        size = 1<<self.k
        for j in range(self.k)[::-1]:
            size = size // 2
            l = self.inner_product(a[size:], G[:size])
            r = self.inner_product(a[:size], G[size:])
            value_l = self.inner_product(a[size:], b[:size])
            value_r = self.inner_product(a[:size], b[size:])
            l_rand = ZZ(self.Fr.random_element())
            r_rand = ZZ(self.Fr.random_element())
            l += ZZ(value_l*z) * U + l_rand * H
            r += ZZ(value_r*z) * U + r_rand * H
            L.append(l)
            R.append(r)
    
            challenge = self.Fr(self.rho(L))
            challenge_inv = challenge**-1
    
            a_new = []
            b_new = []
            G_new = []
            for i in range(size): # parallelizable
                a_new.append(a[i] + ZZ(challenge_inv)*a[i+size])
                b_new.append(b[i] + ZZ(challenge)*b[i+size])
                G_new.append(G[i] + ZZ(challenge)*G[i+size])
            a = a_new
            b = b_new
            G = G_new
            blind += l_rand * challenge_inv
            blind += r_rand * challenge
            rand_l.append(l_rand)
            rand_r.append(r_rand)
        L = L[::-1]
        R = R[::-1]
        assert len(a) == 1 and len(b) == 1 and len(G) == 1
        a = a[0]
        b = b[0]
        G = G[0]
        self.opening = [polynomial(x), C_s, a, L, R, blind]
   
    def verify(self, x):
        v, C_s, a, L, R, blind =  self.opening

        # Recover b and G
        # b = <  prod_i (1+ u_i x^(2*i) , bb  > (computed in O(log(d))
        # G = <s(X),G>                          (computed in O(d))
        b = self.Fr(1)
        sX = self.FrX(1)
        
        T = self.value - ZZ(v) * self.G_bold[0]
        iota = self.Fr(self.rho(C_s))
        T += ZZ(iota) * C_s
        z = self.Fr(self.rho(iota))

        pow_x = x
        powFrX = self.FrX.gen()
        for i in range(len(L)):
            l = L[i]
            r = R[i]
            challenge = self.Fr(self.rho(L[i:][::-1]))
            challenge_inverse = challenge**-1
            T += ZZ(challenge_inverse) * l
            T += ZZ(challenge) * r
            # computation of b and sX, useful for getting G
            b  *= (1 + challenge * pow_x)
            sX *= (1 + challenge * powFrX)
            pow_x  **= 2
            powFrX **= 2
            
        # computation of G with O(d) complexity
        G = self.inner_product(sX.list(), self.G_bold)
        
        U = ZZ(self.Fr(self.rho(x))) * self.Egen
        T += ZZ(-a*b*z) * U + ZZ(a-blind)*self.H + ZZ(-a)*self.H + ZZ(-a)*G
        return T.is_zero()

