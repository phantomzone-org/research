from __future__ import annotations
import random

def poly_add(a: list[int], b: list[int]) -> list[int]:
    assert len(a) == len(b)
    return [ai+bi for (ai,bi) in zip(a,b)]

def poly_sub(a: list[int], b: list[int]) -> list[int]:
    assert len(a) == len(b)
    return [ai-bi for (ai,bi) in zip(a,b)]

def poly_neg(a: list[int]) -> list[int]:
    return [-ai for ai in a]

def negacylic_mul(a: list[int], b:list[int]) -> list[int]:
    assert len(a) == len(b)
    c = [0 for i in range(len(a))]
    for i in range(len(a)):
        for j in range(i+1):
            # print(i, j, i-j)
            c[i] += a[j]*b[i-j]
        for j in range(i+1, len(a)):
            # print(i, j, len(a)-j+i)
            c[i] -= a[j]*b[len(a)-j+i]

    return c

def sample_poly_in_range(ring_size: int, interval: int) -> list[int]:
    return [random.randrange(-interval/2, interval/2) for _ in range(ring_size)]

def embed_small_to_big_ring(a: list[int], big_ring: int) -> list[int]:
    assert len(a) < big_ring

    factor = int(big_ring / len(a))
    out = [0 for _ in range(big_ring)]
    for i in range(len(a)):
        out[factor*i] = a[i]
    return out

def cut_ring(a: list[int], small_ring: int) -> list[int]:
    assert len(a) > small_ring

    factor = int(len(a)/small_ring)
    return [a[i*factor] for i in range(small_ring)]


class KeySwitchingKey:

    def __init__(self, ct: RLWECt) -> None:
        self.ct = ct

    @staticmethod
    def gen_ksk(s_in: Secret, s_out: Secret) -> KeySwitchingKey:
        assert s_in.N() == s_out.N()
        return KeySwitchingKey(ct=s_out.encrypt(m=poly_neg(a=s_in.s)))
    
    def key_switch(self, ct_in: RLWECt) -> RLWECt:
        assert self.ct.Q == ct_in.Q
        assert self.ct.N == ct_in.N

        (b1, a1) = (negacylic_mul(a=ct_in.a, b=self.ct.b), negacylic_mul(a=ct_in.a, b=self.ct.a))
        b1 = poly_add(a=b1, b=ct_in.b)
        return RLWECt(a=a1,b=b1,Q=ct_in.Q,N=ct_in.N)
    

# a = [1, 0, 0, 0]
# b = [1, 0, 0, 0]
# print(negacylic_mul(a=b,b=a))

class Secret():
    def __init__(self, s: list[int], Q: int) -> None:
        self._Q = Q
        self.s=s

    def N(self) -> int:
        return len(self.s)
    
    def Q(self) -> int:
        return self._Q

    @staticmethod
    def new(N: int, Q: int) -> Secret: # type: ignore
        s = [random.randrange(-2, 2) for _ in range(N)]
        return Secret(s=s,Q=Q)
    
    def encrypt(self, m: list[int]):
        assert len(m) == self.N()

        a = sample_poly_in_range(ring_size=self.N(), interval=self.Q())
        b = poly_add(a=negacylic_mul(a, self.s), b=m)
        return RLWECt(a=a, b=b, Q=self.Q(), N=self.N())

        
    def decrypt(self, ct: RLWECt) -> list[int]:
        sa = negacylic_mul(a=self.s, b=ct.a)
        # print("sa=", sa)
        # print("a=",ct.a)
        # print("b=",ct.b)
        return poly_sub(a=ct.b, b=sa)
        
class RLWECt():
    def __init__(self, a: list[int], b: list[int], Q: int, N: int) -> RLWE: # type: ignore
        self.a = a
        self.b = b
        self.Q = Q
        self.N = N

    def cut_ring(self, small_ring: int) -> RLWECt:
        return RLWECt(
            a=cut_ring(a=self.a, small_ring=small_ring), 
            b=cut_ring(a=self.b, small_ring=small_ring),
            Q=self.Q,
            N=small_ring
            )

def test_ring_cut():
    '''
    Test ring switch from N -> N/k for some even k 
    '''
    N = 32
    Nby2 = int(N/4)
    Q = 2**20
    m = sample_poly_in_range(ring_size=N,interval=Q)
    # print('m=',m)
    s0 = Secret.new(N=N,Q=Q)

    ct = s0.encrypt(m=m)
    assert m == s0.decrypt(ct=ct)

    # key switch N -> N
    s1 = Secret.new(N=N,Q=Q)
    ksk_s0s1 = KeySwitchingKey.gen_ksk(s_in=s0, s_out=s1)
    ct_out = ksk_s0s1.key_switch(ct_in=ct)
    assert m == s1.decrypt(ct=ct_out)

    # key switching N -> N/2
    small_s = Secret.new(N=Nby2, Q=Q)
    embed_small_s = Secret(s=embed_small_to_big_ring(a=small_s.s, big_ring=N), Q=Q)
    ksk_s0small_s = KeySwitchingKey.gen_ksk(s_in=s0, s_out=embed_small_s)
    ct_out = ksk_s0small_s.key_switch(ct_in=ct)
    assert m == embed_small_s.decrypt(ct=ct_out)
    ct_Nby2 = ct_out.cut_ring(small_ring=Nby2)
    assert cut_ring(a=m, small_ring=Nby2) == small_s.decrypt(ct=ct_Nby2)

def test_trace():
    # Evaluating Tr_{N/n} zeros are indices i that are not divisible by N/n and require log(N/n) K.S.
    pass






# ring:
#     - (abelian) group under addition
#         - associative
#         - commutative
#         - identity exists
#         - for V a E -a s.t. a + -a = 0
#     - monoid under multiplication
#         - associatve 
#         - identity element exists
#     - distributive over multiplication

# difference between ring and field:
#     - field is a abelian group under multiplication, whereas
#         ring is only a monoid under multiplication