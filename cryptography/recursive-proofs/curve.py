# -*- coding: utf-8 -*-
from sage.all import ZZ
from sage.rings.rational_field import Q as QQ
# from sage.rings.integer_ring import Z as ZZ
from sage.rings.finite_rings.finite_field_constructor import FiniteField as GF
from sage.schemes.elliptic_curves.constructor import EllipticCurve
from sage.functions.other import sqrt
from sage.rings.number_field.number_field import NumberField
from sage.structure.proof.all import arithmetic as ProofArithmetic

ProofArithmetic(False)

class Degree12PairingCurve():
    def __init__(self, p, q, k, PolFpk, alpha=False, beta=False, b=False):
        # alpha is a non-square of Fp defining Fp2. PolFpk defines Fp12/Fp
        self.p = p
        self.q = q
        self.Fp = GF(p)
        self.Fq = GF(q)
        self.k = k

        if b:
            self.E = EllipticCurve([self.Fp(0), self.Fp(b)])
        if not(b):
            b = self.Fp(1)
            self.E = EllipticCurve([self.Fp(0), b])
            while self.E.order() % self.q != 0 :
                b += 1
                self.E = EllipticCurve([self.Fp(0), b])
                self.b = b

        FpT = self.Fp['T']
        T = FpT.gen()
        if not(alpha):
            alpha = self.Fp.random_element()
            polFp2 = T**2 - alpha
            while not(polFp2.is_irreducible()):
                alpha = self.Fp.random_element()
                polFp2 = T**2 - alpha
        alpha = self.Fp(alpha)
        self.polFp2 = T**2 - alpha

        self.Fp2 = GF(self.p**2, 'u', modulus = self.polFp2)
        self.u = self.Fp2.gen()
        
        if not(beta):
            Fp2Z = self.Fp2['Z']
            Z = Fp2Z.gen()
            beta = self.Fp2.random_element()
            polFq6 = Z**6 - beta
            while not(polFq6.is_irreducible()):
                beta = self.Fp2.random_element()
                polFq6 = Z**6 - beta
        self.beta = self.Fp2(beta)

        orderE = self.E.order()
        cof = self.E.order()//self.q
        self.G1 = cof*self.E.random_point()
        while self.G1 == 0:
            self.G1 = cof*self.E.random_point()
        assert self.G1!= 0 and self.q*self.G1==0

        self.E2 = self.E.change_ring(self.Fp2)

        self.E2_t = EllipticCurve([self.Fp2(0), self.beta * self.b])
        self.twist_elt = self.beta
        if self.E2_t.order() % self.q != 0:
            self.twist_elt = self.twist_elt**5
            self.E2_t = EllipticCurve([self.Fp2(0), self.twist_elt * self.b])
        assert self.E2_t.order() % self.q == 0

        cof2 = self.E2_t.order() // self.q
        self.G2 = cof2 * self.E2_t.random_point()
        while self.G2 == 0:
            self.G2 = cof2 * self.E2_t.random_point()

        self.Fpk = GF(self.p**12, 'v', modulus=PolFpk)
        self.v = self.Fpk.gen()
        assert self.beta.minpoly() == (self.v**6).minpoly()

        # The sextic twist is defined using beta:
        # E_{0,b} --> E_{0, twist_elt * b}
        # (x,y)  |--> (twist_elt.sqrt3()*x, twist_elt.sqrt()*y)
        Elt = self.into_Fpk(self.twist_elt)
        self.sqrt_elt = Elt.sqrt()
        Fpkz = self.Fpk['zz']
        zz = Fpkz.gen()
        self.sqrt3_elt = (zz**3 - Elt).roots()[0][0]
        self.Ek = self.E.change_ring(self.Fpk)

        self.G2 = self.into_Ek(self.G2)
        
    def into_Fpk(self, elt):
        # return an Fp2 element in the Fp12 field (which is a
        # Fp-extension)
        # Fp -- x²+1 -- Fp2 -- x⁶-beta -- Fp12
        a = self.beta.polynomial().list()
        if len(a) == 1 :
            a = a + [0]
        e = elt.polynomial().list()
        if len(e) == 1:
            e = e + [0]
        return self.Fp(e[0]) + self.Fp(e[1]) * (self.v**6-self.Fp(a[0])) / self.Fp(a[1])

    def into_Ek(self, pt):
            # return the twisted point to a point of E2_t (i.e. in Ek)
            x = self.into_Fpk(pt[0])
            y = self.into_Fpk(pt[1])
            return self.Ek([x / self.sqrt3_elt, y / self.sqrt_elt])



class BLS12(Degree12PairingCurve):
    def __init__(self, z, polFp12, b=False, alpha=False, beta=False):
        '''
        alpha is a non-square of Fp, defining Fp2
        beta is a non 6-th root of Fp2, defining Fp12 over Fp2
        polFp12 defines Fp12 over Fp, with a well defined injection
        Fp2 --> Fp12.
        '''
        C = ZZ['x']
        x = C.gen()
        p_x = (x-1)**2 * (x**4-x**2+1) + 3*x # needs a division by 3!
        q_x = (x**4-x**2+1)

        super().__init__(p_x(z)//3, q_x(z), 12, polFp12, alpha, beta) 

class BN(Degree12PairingCurve):
    def __init__(self, z, polFp12, b=False, alpha=False, beta=False):
        '''
        alpha is a non-square of Fp, defining Fp2
        beta is a non 6-th root of Fp2, defining Fp12 over Fp2
        polFp12 defines Fp12 over Fp, with a well defined injection
        Fp2 --> Fp12.
        '''
        C = ZZ['x']
        x = C.gen()
        p_x = 36*x**4+36*x**3+24*x**2+6*x+1
        q_x = 36*x**4+36*x**3+18*x**2+6*x+1
    
        super().__init__(p_x(z), q_x(z), 12, polFp12, alpha, beta)

class MNT6():
    def __init__(
            self,
            z,
            polFp6,
            a, b,
            alpha=False,
            beta=False,
            D=False):
        '''
        D is the discriminant if its computation is expensive.
        '''
        C = ZZ['x']
        x = C.gen()
        px = 4*x**2 + 1
        qx = 4*x**2 - 2*x + 1
        self.p = px(z)
        self.Fp = GF(self.p)
        self.q = qx(z)
        self.Fq = GF(self.q)
        self.E = EllipticCurve([self.Fp(a), self.Fp(b)])
        assert (self.q*self.E.random_point()).is_zero()
        self.k = 6

        self.G1 = self.E.random_point()
        while self.G1.is_zero():
            self.G1 = self.E.random_point()
        assert (self.q*self.G1).is_zero()

        FpT = self.Fp['T']
        T = FpT.gen()
        if not(alpha):
            alpha = self.Fp.random_element()
            polFp3 = T**3 - alpha
            while not(polFp3.is_irreducible()):
                alpha = self.Fp.random_element()
                polFp3 = T**3 - alpha
        alpha = self.Fp(alpha)
        polFp3 = T**3 - alpha
        self.Fp3 = GF(self.p**3, 'u', modulus = polFp3)
        self.u = self.Fp3.gen()
        self.E3 = self.E.change_ring(self.Fp3)
        Fp3z= self.Fp3['z']
        z = Fp3z.gen()
        if not(beta):
            beta = self.Fp3.random_element()
            polTower = z**2 - beta
            while not(polTower.is_irreducible()):
                beta = self.Fp3.random_element()
                polTower = z**2 - beta
        beta = self.Fp3(beta)
        polTower = z**2 - beta
        
        self.Fp6 = GF(self.p**6, 'v', modulus = polFp6)
        self.v = self.Fp6.gen()

        assert beta.minpoly() == (self.v**2).minpoly()

        Fp6z = self.Fp6['z']
        z = Fp6z.gen()
        
        u_in_Fp6 = Fp6z(self.u.minpoly()).roots()[0][0]
        def into_Fp6(elt):
            # return an Fp3 element in the Fp6 field (which is a
            # Fp-extension)
            # Fp -- x³-alpha -- Fp3 -- x²-beta -- Fp6
            e = elt.polynomial().list()
            if len(e) == 1:
                e = e + [self.Fp(0),self.Fp(0)]
            if len(e) == 2:
                e = e + [self.Fp(0)]
            return e[0] + e[1] * u_in_Fp6 + e[2] * u_in_Fp6**2
        
        # Quadratic twist is defined using beta
        # E_{a,b} --> E_{beta² * a, beta³ * b}
        # (x,y)  |--> (beta * x, beta**(3/2) * y)
        self.E_3_t = EllipticCurve([
            beta**2 * self.E.a4(),
            beta**3 * self.E.a6()
        ])
        self.E_3 = self.E.change_ring(self.Fp3)
        self.Ek = self.E.change_ring(self.Fp6)
        sqrt_beta_Fp6 = (z**2 - into_Fp6(beta)).roots()[0][0]
        
        def into_Ek(pt):
            # return the twisted point to a point of E_3_t (i.e a point of Ek
            x = into_Fp6(pt[0]/pt[2])
            y = into_Fp6(pt[1]/pt[2])
            return self.Ek([x / into_Fp6(beta),
                         y / into_Fp6(beta) / sqrt_beta_Fp6])
        # the trace over Fp is known by construction
        t = self.p+1-self.q
        assert (self.p+1-t)*self.E.random_point() == 0
        
        # we obtain the trace over Fp3 using the frobenius seen in \mathbb C
        if not(D) :
            D = ZZ(t**2 - 4 * self.p).squarefree_part()
        y = ZZ(sqrt((t**2 - 4 * self.p) // D))
        assert D*y**2 == t**2 - 4 * self.p
        
        QQX = QQ['X']
        X = QQX.gen()
        K = NumberField(X**2 - D, 'pi')
        pi = K.gen()
        r1 = (t + pi * y)/2
        r2 = r1.conjugate()
        assert r1 + r2 == t
        
        t_3 = ZZ(r1**3 + r2**3)
        assert (self.p**3 + 1 - t_3)*self.E_3.random_point() == 0
        assert (self.p**3 + 1 + t_3)*self.E_3_t.random_point() == 0
        
        E_3_t_order = self.p**3 + 1 + t_3
        # Sample an element of G2 using the sextic twist
        cof = E_3_t_order // self.q
        self.G2 = cof*self.E_3_t.random_point()
        while self.G2.is_zero():
            self.G2 = cof*self.E_3_t.random_point()
        self.G2 = into_Ek(self.G2)
        
class MNT4():
    def __init__(
            self,
            z,
            polFp4,
            a, b,
            alpha=False,
            beta=False,
            D=False):
        '''
        D is the discriminant if its computation is expensive.
        '''
        C = ZZ['x']
        x = C.gen()
        px = x**2 + x + 1
        qx = x**2 + 1
        self.p = px(z)
        self.Fp = GF(self.p)
        self.q = qx(z)
        self.Fq = GF(self.q)
        self.E = EllipticCurve([self.Fp(a), self.Fp(b)])
        assert (self.q*self.E.random_point()).is_zero()
        self.k = 4

        self.G1 = self.E.random_point()
        while self.G1.is_zero():
            self.G1 = self.E.random_point()
        assert (self.q*self.G1).is_zero()

        FpT = self.Fp['T']
        T = FpT.gen()
        if not(alpha):
            alpha = self.Fp.random_element()
            polFp2 = T**2 - alpha
            while not(polFp2.is_irreducible()):
                alpha = self.Fp.random_element()
                polFp2 = T**2 - alpha
        alpha = self.Fp(alpha)
        polFp2 = T**2 - alpha
        self.Fp2 = GF(self.p**2, 'u', modulus = polFp2)
        self.u = self.Fp2.gen()
        self.E2 = self.E.change_ring(self.Fp2)
        Fp2z= self.Fp2['z']
        z = Fp2z.gen()
        if not(beta):
            beta = self.Fp2.random_element()
            polTower = z**2 - beta
            while not(polTower.is_irreducible()):
                beta = self.Fp2.random_element()
                polTower = z**2 - beta
        beta = self.Fp2(beta)
        polTower = z**2 - beta
        
        self.Fp4 = GF(self.p**4, 'v', modulus = polFp4)
        self.v = self.Fp4.gen()

        assert beta.minpoly() == (self.v**2).minpoly()

        Fp4z = self.Fp4['z']
        z = Fp4z.gen()
        
        u_in_Fp4 = Fp4z(self.u.minpoly()).roots()[0][0]
        def into_Fp4(elt):
            # return an Fp2 element in the Fp4 field (which is a
            # Fp-extension)
            # Fp -- x²-alpha -- Fp2 -- x²-beta -- Fp4
            e = elt.polynomial().list()
            if len(e) == 1:
                e = e + [self.Fp(0)]
            return e[0] + e[1] * u_in_Fp4
        
        # Quadratic twist is defined using beta
        # E_{a,b} --> E_{beta² * a, beta³ * b}
        # (x,y)  |--> (beta * x, beta**(3/2) * y)
        self.E_2_t = EllipticCurve([
            beta**2 * self.E.a4(),
            beta**3 * self.E.a6()
        ])
        self.E_2 = self.E.change_ring(self.Fp2)
        self.Ek = self.E.change_ring(self.Fp4)
        sqrt_beta_Fp4 = (z**2 - into_Fp4(beta)).roots()[0][0]
        
        def into_Ek(pt):
            # return the twisted point to a point of E_3_t (i.e a point of Ek
            x = into_Fp4(pt[0]/pt[2])
            y = into_Fp4(pt[1]/pt[2])
            return self.Ek([x / into_Fp4(beta),
                            y / into_Fp4(beta) / sqrt_beta_Fp4])
        # the trace over Fp is known by construction
        t = self.p+1-self.q
        assert (self.p+1-t)*self.E.random_point() == 0
        
        # we obtain the trace over Fp3 using the frobenius seen in \mathbb C
        if not(D) :
            D = ZZ(t**2 - 4 * self.p).squarefree_part()
        y = ZZ(sqrt((t**2 - 4 * self.p) // D))
        assert D*y**2 == t**2 - 4 * self.p
        
        QQX = QQ['X']
        X = QQX.gen()
        K = NumberField(X**2 - D, 'pi')
        pi = K.gen()
        r1 = (t + pi * y)/2
        r2 = r1.conjugate()
        assert r1 + r2 == t
        
        t_2 = ZZ(r1**2 + r2**2)
        assert (self.p**2 + 1 - t_2)*self.E_2.random_point() == 0
        assert (self.p**2 + 1 + t_2)*self.E_2_t.random_point() == 0
        
        E_2_t_order = self.p**2 + 1 + t_2
        # Sample an element of G2 using the sextic twist
        cof = E_2_t_order // self.q
        self.G2 = cof*self.E_2_t.random_point()
        while self.G2.is_zero():
            self.G2 = cof*self.E_2_t.random_point()
        self.G2 = into_Ek(self.G2)
        
