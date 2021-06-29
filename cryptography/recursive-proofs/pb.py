# -*- coding: utf-8 -*-
import hashlib
import sage.all
from sage.rings.integer_ring import Z as ZZ
from sage.rings.finite_rings.finite_field_constructor import FiniteField as GF
from sage.schemes.elliptic_curves.constructor import EllipticCurve
from curve import *
from sage.misc.misc import cputime
from sage.misc.functional import cyclotomic_polynomial
from sage.matrix.constructor import Matrix
from sage.misc.prandom import randint
from sage.modules.free_module_element import free_module_element as vector

def rho(*arg):
    return int(hashlib.sha256((str(arg)).encode()).hexdigest(),16)

def vector_to_lagrange_poly(vec,MatLagrange_inverse) :
    while len(vec) < MatLagrange_inverse.nrows() :
        vec = vec + [0]
    return (MatLagrange_inverse * vector(list(vec))).list() # seen in FqX
        
class TrustedSetup():
    def __init__(self, curve, k):
        """
        Setup everything for the proof scheme, including the SRS
        trusted setup using a random scalar s.
        """
        
        self.p = curve.p
        self.q = curve.q
        self.Fp = GF(self.p)
        self.Fq = GF(self.q)
        self.E = curve.G1.parent()
        self.Ek = curve.G2.parent()
        self.G1 = curve.G1
        self.G2 = curve.G2
        self.embedding_degree = curve.k
        self.k = k
        self.n = 1<<k

        # roots of unity
        
        self.FqX = self.Fq['X']
        X = self.FqX.gen()
        ZHX = X**self.n - 1
        self.ZHX =ZHX
        ZHX_roots = ZHX.roots()
        assert len(ZHX_roots) == self.n
        H = [x[0] for x in ZHX_roots]
        iH = iter(H)
        phi_n = cyclotomic_polynomial(self.n)
        for omega in iH :
            if phi_n(omega) == 0 :
                break
            else :
                next(iH)
        self.omega = omega
        self.H = [omega**i for i in range(self.n)]
        self.MatLagrange = \
            Matrix([[omega**i for i in range(self.n)] for omega in self.H])
        
        # k1 and k2
        self.k1 = self.Fq.random_element()
        while self.k1 in H or self.k1.is_square():
            self.k1 = self.Fq.random_element()
        self.k2 = self.Fq.random_element()
        while self.k2 in H or self.k2/self.k1 in H or self.k2.is_square() :
            self.k2 = self.Fq.random_element()

        # trusted part of the setup
        self.values = [self.G1]
        s = ZZ(self.Fq.random_element())
        for i in range(self.n+2):
            self.values.append(s * self.values[-1])
        self.values.append(self.G2)
        self.values.append(s*self.G2)

    def eval_poly(self, poly):
        """
        compute [f(s)] G1 using the trusted setup,
        i.e. without knowing s.
        """

        L = poly.list()
        res = 0
        for i in range(len(L)):
            res += ZZ(L[i]) * self.values[i]
        return res


class Circuit():
    def __init__(self, trusted_setup, L, R, O, M, C, S1, S2, S3, a, b, c):

        # resizing
        L = L + [0 for i in range(trusted_setup.n - len(L))]
        R = R + [0 for i in range(trusted_setup.n - len(R))]
        O = O + [0 for i in range(trusted_setup.n - len(O))]
        M = M + [0 for i in range(trusted_setup.n - len(M))]
        C = C + [0 for i in range(trusted_setup.n - len(C))]
        a = a + [0 for i in range(trusted_setup.n - len(a))]
        b = b + [0 for i in range(trusted_setup.n - len(b))]
        c = c + [0 for i in range(trusted_setup.n - len(c))]
        while len(S1) < trusted_setup.n :
            S1.append(trusted_setup.H[len(S1)])
        while len(S2) < trusted_setup.n :
            S2.append(trusted_setup.k1 * trusted_setup.H[len(S2)])
        while len(S3) < trusted_setup.n :
            S3.append(trusted_setup.k2 * trusted_setup.H[len(S3)])

        # without Lagrange interpolation
        self._L = L
        self._R = R
        self._O = O
        self._M = M
        self._C = C
        self._a = a
        self._b = b
        self._c = c
        self._S1 = S1
        self._S2 = S2
        self._S3 = S3
            
        # with Lagrange interpolation
        MatLagrange_inverse = trusted_setup.MatLagrange**-1
        self.L = (MatLagrange_inverse * vector(L)).list()
        self.R = (MatLagrange_inverse * vector(R)).list()
        self.O = (MatLagrange_inverse * vector(O)).list()
        self.M = (MatLagrange_inverse * vector(M)).list()
        self.C = (MatLagrange_inverse * vector(C)).list()
        self.S1 =(MatLagrange_inverse * vector(S1)).list()
        self.S2 =(MatLagrange_inverse * vector(S2)).list()
        self.S3 =(MatLagrange_inverse * vector(S3)).list()
        self.a = (MatLagrange_inverse * vector(a)).list()
        self.b = (MatLagrange_inverse * vector(b)).list()
        self.c = (MatLagrange_inverse * vector(c)).list()

        # Into G1
        self.L_G1 = trusted_setup.eval_poly(trusted_setup.FqX(self.L))
        self.R_G1 = trusted_setup.eval_poly(trusted_setup.FqX(self.R))
        self.O_G1 = trusted_setup.eval_poly(trusted_setup.FqX(self.O))
        self.M_G1 = trusted_setup.eval_poly(trusted_setup.FqX(self.M))
        self.C_G1 = trusted_setup.eval_poly(trusted_setup.FqX(self.C))
        self.S1_G1 =trusted_setup.eval_poly(trusted_setup.FqX(self.S1))
        self.S2_G1 =trusted_setup.eval_poly(trusted_setup.FqX(self.S2))
        self.S3_G1 =trusted_setup.eval_poly(trusted_setup.FqX(self.S3))
        self.a_G1 = trusted_setup.eval_poly(trusted_setup.FqX(self.a))
        self.b_G1 = trusted_setup.eval_poly(trusted_setup.FqX(self.b))
        self.c_G1 = trusted_setup.eval_poly(trusted_setup.FqX(self.c))


class PbProof():
    
    def __init__(self, SRS):
        """
        Fill srs using the SRS.
        """
        self.srs = SRS
        self.proof = []

    def create(self, a, b, c, circuit, bench=False):
        """
        create a proof for the circuit `circuit`, together with the
        knowledge of `a`, `b` and `c`.
        """

        X = self.srs.FqX.gen()
        
        faX,fbX,fcX,qLX,qRX,qOX,qMX,qCX,Ss1X,Ss2X,Ss3X = \
            [self.srs.FqX(f) for f in [circuit.a,circuit.b,circuit.c,circuit.L,circuit.R,circuit.O,circuit.M,circuit.C,circuit.S1,circuit.S2,circuit.S3]]
        
        # 1
        if bench:
            t = cputime()
        b1,b2,b3,b4,b5,b6 = [self.srs.Fq.random_element() for i in range(6)]
        aX = (b1*X+b2) * self.srs.ZHX + faX
        bX = (b3*X+b4) * self.srs.ZHX + fbX
        cX = (b5*X+b6) * self.srs.ZHX + fcX
        self.proof = [self.srs.eval_poly(pol) for pol in [aX,bX,cX]]
        if bench:
            print('1:', round(cputime(t), 2), "s")

        # 2
        if bench:
            t = cputime()
        beta  = self.srs.Fq(rho(self.proof, 0))
        gamma = self.srs.Fq(rho(self.proof, 1))
        
        b7,b8,b9 = [self.srs.Fq.random_element() for i in range(3)]
        acc = self.srs.Fq(1)
        acc_vec = [acc]

        _omega = 1
        for i in range(self.srs.n-1):
            # _omega = omega**i
            num = (circuit._a[i] + beta*_omega + gamma) * \
                (circuit._b[i] + beta * self.srs.k1 * _omega + gamma) * \
                (circuit._c[i] + beta * self.srs.k2 * _omega + gamma)
            den = (circuit._a[i]+beta*circuit._S1[i] + gamma) * \
                (circuit._b[i] + beta*circuit._S2[i] + gamma) * \
                (circuit._c[i] + beta*circuit._S3[i] + gamma)
            acc *= num/den
            acc_vec.append(acc)
            _omega *= self.srs.omega
        assert acc == 1
        accX = self.srs.FqX(vector_to_lagrange_poly(acc_vec, self.srs.MatLagrange**-1))
        zX = (b7*X**2 + b8*X+b9) * self.srs.ZHX + accX
        self.proof.append(self.srs.eval_poly(zX))
        if bench:
            print('2:', round(cputime(t), 2), "s")
    
        # 3
        if bench:
            t = cputime()
        alpha = self.srs.Fq(rho(self.proof))
        L1X = self.srs.FqX(vector_to_lagrange_poly([1,0,0,0],
        self.srs.MatLagrange**-1))
                                
        tX,tmp = ((aX*bX*qMX + aX*qLX + bX*qRX + cX*qOX + qCX) + \
            ((aX + beta*X + gamma) * (bX + beta*self.srs.k1*X + gamma) * (cX +
            beta*self.srs.k2*X + gamma) * zX) * alpha - \
            ((aX+beta * Ss1X + gamma) * (bX + beta * Ss2X + gamma) \
             * (cX + beta*Ss3X + gamma) * zX(X*self.srs.omega)) * alpha + \
                       (zX - 1) * L1X * alpha**2).quo_rem(self.srs.ZHX)
        assert tmp == 0
        tloX = tX.mod(X**(self.srs.n+2))
        tmidX = ((tX - tloX) // (X**(self.srs.n+2))).mod(X**(self.srs.n+2))
        thiX = (tX - tloX - X**(self.srs.n+2) * tmidX ) // (X**(2*self.srs.n+4))
        self.proof.extend([self.srs.eval_poly(pol) for pol in
        [tloX,tmidX,thiX]])
        if bench:
            print('3:', round(cputime(t), 2), "s")
        
        # 4
        if bench:
            t = cputime()
        z = self.srs.Fq(rho(self.proof))
        abar,bbar,cbar,Ss1bar,Ss2bar,tbar,zwbar = \
        aX(z),bX(z),cX(z),Ss1X(z),Ss2X(z),tX(z),zX(self.srs.omega*z)
        rX = abar * bbar * qMX + abar * qLX + bbar * qRX + cbar * qOX + qCX \
            + ((abar + beta*z+gamma) * (bbar + beta*self.srs.k1*z + gamma) *
              (cbar + beta * self.srs.k2 * z + gamma) * zX) * alpha \
            - ((abar + beta*Ss1bar + gamma) * (bbar + beta * Ss2bar + gamma) *
              beta*zwbar * Ss3X) * alpha \
            + zX*L1X(z)*alpha**2
        rbar = rX(z)
        self.proof.extend([abar,bbar,cbar,Ss1bar,Ss2bar,zwbar,rbar])
        if bench:
            print('4:', round(cputime(t), 2), "s")
        
        # 5
        if bench:
            t = cputime()
        v = self.srs.Fq(rho(self.proof))
        WzX = (tloX + z**(self.srs.n+2) * tmidX + \
               z**(2*self.srs.n+4) * thiX - tbar + \
               v* (rX - rbar) + \
               v**2 *(aX - abar) + \
               v**3 *(bX- bbar) + \
               v**4 *(cX - cbar) + \
               v**5 *(Ss1X - Ss1bar) + \
               v**6 *(Ss2X- Ss2bar)
        ) / (X-z)
        WzwX = (zX - zwbar) / (X - z*self.srs.omega)
        WzX = self.srs.FqX(WzX)
        WzwX = self.srs.FqX(WzwX)
        self.proof.extend([self.srs.eval_poly(pol) for pol in [WzX,
        WzwX]])
        if bench:
            print('5:', round(cputime(t), 2), "s")

    def verify(self, circuit, for_accumulator=False, bench=False):

        _a,_b,_c,_z,_tlo,_tmid,_thi, \
            _abar,_bbar,_cbar,_s1bar,_s2bar,_zwbar,_rbar,_Wz,_Wzw \
            = self.proof

        X = self.srs.FqX.gen()

        _qL, _qR, _qO, _qM, _qC, _Ss1,_Ss2,_Ss3 = \
            [circuit.L_G1,circuit.R_G1,circuit.O_G1,circuit.M_G1,circuit.C_G1,circuit.S1_G1,circuit.S2_G1,circuit.S3_G1]

        if bench:
            t = cputime()            
        beta  = self.srs.Fq(rho(self.proof[:3], 0))
        gamma = self.srs.Fq(rho(self.proof[:3], 1))
        alpha = self.srs.Fq(rho(self.proof[:4]))
        z     = self.srs.Fq(rho(self.proof[:7]))
        v     = self.srs.Fq(rho(self.proof[:14]))
        if bench:
            print('2:', round(cputime(t), 2), "s")
            t = cputime()

        ZHz = z**self.srs.n -1
        L1z = (z**self.srs.n - 1) / (self.srs.n*(z-1))
        tbar2 = (
            _rbar
            - (
                (_abar + beta * _s1bar + gamma)
                * (_bbar + beta * _s2bar + gamma)
                * (_cbar + gamma)
                * _zwbar
            ) * alpha - L1z * alpha**2
        ) / ZHz
        if bench :
            print('3:', round(cputime(t), 2), "s")
            t = cputime()

        u = self.srs.Fq.random_element()
        
        _D = ZZ(_abar * _bbar * v) * _qM \
        + ZZ(_abar * v) * _qL \
        + ZZ(_bbar * v) *_qR \
        + ZZ(_cbar * v) *_qO \
        + ZZ(v) *_qC \
        + ZZ( \
              (_abar + beta*z + gamma) \
            * (_bbar + beta*self.srs.k1*z + gamma) \
            * (_cbar + beta*self.srs.k2*z + gamma) \
            * alpha * v + L1z * alpha**2*v + u \
            )*_z \
        - ZZ( \
            (_abar + beta*_s1bar + gamma) \
            * (_bbar + beta*_s2bar + gamma) \
            * alpha*v*beta*_zwbar
            )* _Ss3
        
        if bench:
            print('4:', round(cputime(t), 2), "s")
            t = cputime()
        
        _F = _tlo \
            + ZZ(z**(self.srs.n+2))*_tmid \
            + ZZ(z**(2*self.srs.n+4)) * _thi \
            + _D \
            + ZZ(v**2) * _a \
            + ZZ(v**3) * _b \
            + ZZ(v**4) * _c \
            + ZZ(v**5) * _Ss1 \
            + ZZ(v**6) * _Ss2

        if bench:
            print('5:', round(cputime(t), 2), "s")
            t = cputime()
            
        _E = ZZ(
            tbar2 \
            + v*_rbar + v**2*_abar + v**3 *_bbar + v**4 *_cbar + v**5 *
            _s1bar \
            + v**6 * _s2bar + u*_zwbar
            ) * self.srs.G1

        if bench:
            print('6:', round(cputime(t), 2), "s")
            t = cputime()
            
        tmp_1 = self.srs.G2.curve()(_Wz + ZZ(u) * _Wzw)
        tmp_2 = self.srs.G2.curve()(ZZ(z) * _Wz + ZZ(u*z*self.srs.omega) * _Wzw + _F -
        _E)

        if bench:
            print(round(cputime(t), 2), "s")
        
        if for_accumulator :
            return tmp_1,tmp_2
        else :
            if bench:
                t = cputime()
            boo = tmp_1.tate_pairing(self.srs.values[-1], self.srs.q, self.srs.embedding_degree) == \
                tmp_2.tate_pairing(self.srs.values[-2], self.srs.q,
            self.srs.embedding_degree)
            if bench:
                print('7:', round(cputime(t), 2), "s")
            return boo
