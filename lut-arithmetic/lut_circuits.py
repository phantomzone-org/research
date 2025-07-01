from __future__ import annotations
import math
import random
from utils import bits_to_signed_int, bits_to_unsigned_int, signed_int_to_bin_list, unsigned_int_to_bin_list


def int_to_log_beta_list(val, log_beta, max_bits):
    """
    Convert an integer n to a list of digits in base b (in little endian)
    """
    digits = []
    b = 1<<log_beta
    while val > 0 or len(digits) < (max_bits//log_beta):
        digits.append(val % b)
        val //= b
    return digits

def generate_gp_or_lut() -> LUT:
    lut: dict[int: int] = {}
    for i in range(1<<4):
        # p OR g
        # values are stored as 0|p|0|p
        lut[i] = ((i & (1<<2)) >> 2) | (i & 1)
    return LUT(lut=lut,lut_precision_bits=4)


def generate_log_beta_identity_lut(log_beta: int, lut_precision_bits: int) -> LUT:
    """
    LUT that maps v -> u where v \in [0, 2^lut_precision) and u are least 
    significant beta bits (& u is always \in [0,2^log_beta)])
    """
    max_value = 1 << lut_precision_bits

    lut: dict[int: int]  = {}
    for i in range(max_value):
        # extract LSB log_beta bits
        lut[i] = i & ((1<<log_beta)-1)
    return LUT(lut=lut, lut_precision_bits=lut_precision_bits)

def generate_limbs_to_gp_lut_for_first_limb(log_beta: int, carry_in: bool) -> LUT: 
    """
    LUT that maps (the first limbs) a0, b0 \in 2^log_beta to generator bit g0 and propogator*carry_in bit p0*c_in for the
    look ahead carry adder. (note: c1 = g0 + p0 * c_in)

    The output of LUT are expected to be used directly in the recursive algorithm that calculates next carry bits, thus, since
    the 0^th limb accounts for the carry_in, g0 and p0*c_in are provided (not g0 and p0)

    Bits p0*c0 and g0 are packed as 0|p0*c0|0|g. This ensures that LUT for recusion function 
    (p_out, g_out) = (p_in1 p_in2, p_in1 g_in2 + g_in1) is computed with scaling factor 2.

    LUT requires precision of 2*log_beta bits and the LWE parameters should 
    support, at the minimum, correctness for lwe ciphertext constructed as c=2^{log_beta}*a+b 
    """
    beta = 1 <<log_beta
    carry_in = int(carry_in)
    lut: dict[int: int] = {}
    for i in range(beta):
        for j in range(beta):
            g = (i+j) // beta
            p = (i+j+1) // beta
            lut[(i<<log_beta)+j] = ((p*carry_in)<<2)+g
            # a0|b0 -> 0|p*c_in|0|g 
    return LUT(lut=lut, lut_precision_bits=2*log_beta)

def generate_limbs_to_gp_lut(log_beta: int) -> LUT: 
    """
    LUT that maps limbs ai, bi \in 2^log_beta to generator and propogator bits
    for look ahead carry adder. 

    LUT requires precision of 2*log_beta bits and the LWE parameters should 
    support, at the minimum, correctness for lwe ciphertext constructed as c=2^{log_beta}*a+b 

    Generator bit g indicates whether summation ai+bi generates a carry bit. Propogator bit
    p indicates whether summaiton ai+bi propogates the incoming carry bit. 

    g = ai+bi // 2^log_beta
    p = ai+bi+1 // 2^log_beta

    Bits p and g are packed as 0|p|0|g. This ensures that LUT for recusion function 
    (p_out, g_out) = (p_in1 p_in2, p_in1 g_in2 + g_in1) is computed with scaling factor 2.
    """
    beta = 1 <<log_beta
    lut: dict[int: int] = {}
    for i in range(beta):
        for j in range(beta):
            g = (i+j) // beta
            p = (i+j+1) // beta
            # a0|b0 -> 0|p|0|g 
            lut[(i<<log_beta)+j] = (p<<2)+g
    return LUT(lut=lut, lut_precision_bits=2*log_beta)

def generate_gp_recursion_lut() -> LUT:
    """
    LUT for recusion function (p_out, g_out) = (p_in1 p_in2, p_in1 g_in2 + g_in1)

    Recusion function requires LUT of precision 4 bits

    LWE parameters must support, at the minimum, LUT correctness for LWE ciphertext
    c = 2*a+b
    """
    # g_in, p_in = g0,p0
    # g_out, p_out = g1,p1
    # values are packed as p0p1g0g1. Compute function (p0p1, g0+p0g1)
    lut: dict[int: int] = {}
    for p0 in [0,1]:
        for p1 in [0,1]:
            for g0 in [0,1]:
                for g1 in [0,1]:
                    gout = int(bool(g0) or (bool(p0) and bool(g1)))
                    pout = int(bool(p0) and bool(p1))
                    lut[(p0<<3)+(p1<<2)+(g0<<1)+g1] = (pout<<2)+gout
    return LUT(lut=lut, lut_precision_bits=4)

def calc_carries(lwects_in: list[LWECt], start: int, end: int, gp_lut: LUT):
    """
    Calculate the carries in log n depth where n are no. of limbs. 

    Requires n/2 * log n LUTs
    """
    # print(start, end)

    if (end-start) == 2:
        # pack gp values: p_in1|p_in2|g_in1|g_in2 = 2*lwe_in+lwe_out
        tmp_lwe = LWECt(val=2*lwects_in[end-1].val+lwects_in[start].val, lut_precision_bits=lwects_in[0].lut_precision_bits)
        lwects_in[end-1] = tmp_lwe.eval_lut(gp_lut)
        return
    
    mid = (end+start)//2

    # in parallel
    calc_carries(lwects_in=lwects_in, start=start, end=mid, gp_lut=gp_lut)
    calc_carries(lwects_in=lwects_in, start=mid, end=end,gp_lut=gp_lut)

    #  (g,p)_i • (g,p)_{mid-1} for i \in [mid,end)
    for i in range(mid, end):
        # (g,p)_i = (g,p)_in1
        tmp_lwe = LWECt(val=2*lwects_in[i].val+lwects_in[mid-1].val, lut_precision_bits=lwects_in[0].lut_precision_bits)
        lwects_in[i] = tmp_lwe.eval_lut(lut=gp_lut)

def add_circuit(a_limbsct: list[LWECt], b_limbsct: list[LWECt], log_beta: int, total_bits: int) -> tuple[list[LWECt], int , int]:
    limb_count = total_bits // log_beta
    assert len(a_limbsct) == limb_count
    assert len(b_limbsct) == limb_count

    lut_count = 0
    lut_depth = 0

    gp_lut_first_limb = generate_limbs_to_gp_lut_for_first_limb(log_beta=log_beta, carry_in=False)
    gp_lut = generate_limbs_to_gp_lut(log_beta=log_beta)

    gp_list: list[LWECt] = []
    # calculate gi,pi in parallel
    for i in range(limb_count):
        # \beta*ai+bi
        tmp = LWECt(val=(1<<log_beta)*a_limbsct[i].val+b_limbsct[i].val, lut_precision_bits=b_limbsct[i].lut_precision_bits)
        gp_i = None
        if i == 0:
            gp_i = tmp.eval_lut(lut=gp_lut_first_limb)
        else: 
            gp_i = tmp.eval_lut(lut=gp_lut)
        gp_list.append(gp_i)
        lut_count+=1
    lut_depth+=1

    calc_carries(lwects_in=gp_list, start=0, end=len(gp_list),gp_lut=generate_gp_recursion_lut())
    lut_count += (limb_count//2) * int(math.log2(limb_count))
    lut_depth += int(math.log2(limb_count))

    # si = ai+bi+ci // no bootstrapping
    gp_list = [LWECt(val=0, lut_precision_bits=0)] + gp_list # incoming carry c0 is always 0
    summands_list = [LWECt(val=ai.val+bi.val+ci.val, lut_precision_bits=ai.lut_precision_bits) for (ai,bi,ci) in zip(a_limbsct, b_limbsct, gp_list)]

    # clean carry overs, in parallel
    log_beta_identity_lut = generate_log_beta_identity_lut(log_beta=log_beta, lut_precision_bits=a_limbsct[0].lut_precision_bits)
    final_sum_list = [a.eval_lut(lut=log_beta_identity_lut) for a in summands_list]
    lut_depth += 1
    lut_count += limb_count

    return (final_sum_list, lut_depth, lut_count)

def sub_circuit(a_limbsct: list[LWECt], b_limbsct: list[LWECt], log_beta: int, total_bits: int) -> tuple[list[LWECt], int , int]:
    limb_count = total_bits // log_beta
    assert len(a_limbsct) == limb_count
    assert len(b_limbsct) == limb_count

    lut_count = 0
    lut_depth = 0

    # compute 2's complement of b: LWE(bi') = (2^log_beta - 1) - LWE(bi)
    b_limbsct_twos_compl = [LWECt(val=(((1<<log_beta)-1) - bi.val), lut_precision_bits=bi.lut_precision_bits) for bi in b_limbsct]

    gp_lut_first_limb = generate_limbs_to_gp_lut_for_first_limb(log_beta=log_beta, carry_in=True)
    gp_lut = generate_limbs_to_gp_lut(log_beta=log_beta)

    # ADD: a + b'
    # compute gi,pi in parallel
    gp_list: list[LWECt] = []
    for i in range(limb_count):
        # \beta*ai+bi
        tmp = LWECt(val=(1<<log_beta)*a_limbsct[i].val+b_limbsct_twos_compl[i].val, lut_precision_bits=b_limbsct_twos_compl[i].lut_precision_bits)
        gp_i = None
        if i == 0:
            gp_i = tmp.eval_lut(lut=gp_lut_first_limb)
        else: 
            gp_i = tmp.eval_lut(lut=gp_lut)
        gp_list.append(gp_i)
        lut_count+=1
    lut_depth+=1

    calc_carries(lwects_in=gp_list, start=0, end=len(gp_list),gp_lut=generate_gp_recursion_lut())
    lut_count += (limb_count//2) * int(math.log2(limb_count))
    lut_depth += int(math.log2(limb_count))

    # In case of subtraction, carry_in is set to 1. Hence, pi may not always be 0 (in addition pi is expected to be zero). The carry ci equals gi or pi.
    # Use LUT to collapse gi or pi into ci
    gp_or_lut = generate_gp_or_lut()
    # in parallel
    gp_list = [ai.eval_lut(lut=gp_or_lut) for ai in gp_list]
    lut_depth+=1
    lut_count+=limb_count

    # si = ai+bi+ci
    gp_list = [LWECt(val=1, lut_precision_bits=0)] + gp_list
    summands_list = [LWECt(val=ai.val+bi.val+ci.val, lut_precision_bits=ai.lut_precision_bits) for (ai,bi,ci) in zip(a_limbsct, b_limbsct_twos_compl, gp_list)]

    # clean carry overs, in parallel
    log_beta_identity_lut = generate_log_beta_identity_lut(log_beta=log_beta, lut_precision_bits=a_limbsct[i].lut_precision_bits)
    final_sum_list = [a.eval_lut(lut=log_beta_identity_lut) for a in summands_list]
    lut_depth += 1
    lut_count += limb_count

    return (final_sum_list, lut_depth, lut_count)

def test_add_circuit():
    # 2^log_beta is the limb base
    log_beta = 2
    total_bits = 32

    lut_precision = 1<<(log_beta*2)

    a = random.randint(a=0, b=(1<<total_bits)-1)
    b = random.randint(a=0, b=(1<<total_bits)-1)
    a_cts = [LWECt(val=v, lut_precision_bits=lut_precision) for v in int_to_log_beta_list(val=a, log_beta=log_beta, max_bits=total_bits)]
    b_cts = [LWECt(val=v, lut_precision_bits=lut_precision) for v in int_to_log_beta_list(val=b, log_beta=log_beta, max_bits=total_bits)]

    (final_sum_cts, lut_depth, lut_count) = add_circuit(a_limbsct=a_cts, b_limbsct=b_cts, log_beta=log_beta, total_bits=total_bits)

    print("Add circuit: ")
    print(" LUT depth=", lut_depth)
    print(" LUT count=", lut_count)

    final_sum = 0
    for (index, ct) in enumerate(final_sum_cts):
        final_sum += ((1<<(log_beta*index))*ct.val)
    assert final_sum == ((a+b) % (1<<total_bits))

def test_sub_circuit():
    log_beta = 2
    total_bits = 32

    lut_precision = 1<<(log_beta*2)

    a = random.randint(a=0, b=(1<<total_bits)-1)
    b = random.randint(a=0, b=(1<<total_bits)-1)
    a_cts = [LWECt(val=v, lut_precision_bits=lut_precision) for v in int_to_log_beta_list(val=a, log_beta=log_beta, max_bits=total_bits)]
    b_cts = [LWECt(val=v, lut_precision_bits=lut_precision) for v in int_to_log_beta_list(val=b, log_beta=log_beta, max_bits=total_bits)]

    (final_sum_cts, lut_depth, lut_count) = sub_circuit(a_limbsct=a_cts, b_limbsct=b_cts, log_beta=log_beta, total_bits=total_bits)

    print("Add circuit: ")
    print(" LUT depth=", lut_depth)
    print(" LUT count=", lut_count)

    final_sum = 0
    for (index, ct) in enumerate(final_sum_cts):
        final_sum += ((1<<(log_beta*index))*ct.val)
    # print(final_sum, ((a-b) % (1<<total_bits)))
    assert final_sum == ((a-b) % (1<<total_bits))


class LUT():
    def __init__(self, lut: dict[int: int], lut_precision_bits) -> None:
        """
        `lut`: LUT dictionary
        `lut_precision`: Minimum no. of precision bits required to evaluate the LUT
        """

        self.lut = lut
        self.lut_precision_bits = lut_precision_bits

    def print_as_is(self):
        """Print the dictionary as is (i.e. as ints)"""
        for k, v in self.lut.items():
            print(f"{k}: {v}")

    def print_in_base_logbeta(self, log_beta):
        """Print the dictionary with integers represented in base 2^log_beta."""
        for k, v in self.lut.items():
            k_digits = int_to_log_beta_list(k, log_beta, self.lut_precision_bits)[::-1]
            v_digits = int_to_log_beta_list(v, log_beta, self.lut_precision_bits)[::-1]
            print(f"{k_digits}: {v_digits}")

class LWECt():
    def __init__(self, val, lut_precision_bits: int, ) -> None:
        self.val = val
        self.lut_precision_bits = lut_precision_bits

    def eval_lut(self, lut: LUT) -> LWECt:
        assert lut.lut_precision_bits <= self.lut_precision_bits
        assert lut.lut[self.val] is not None
        return LWECt(val=lut.lut[self.val], lut_precision_bits=self.lut_precision_bits)

    def __str__(self) -> str:
        return f"LWECt(val={self.val})"
    







# a0 = -2343
# b0 = -2
# # a1 = 35554

# # b1 = 1312

# a0_list = unsigned_int_to_bin_list(val=a0, max_bits=32)
# # a1_list = int_to_bin_list(val=a1, max_bits=32)
# b0_list = unsigned_int_to_bin_list(val=b0, max_bits=32)
# b0_list[-1] = -1
# b1_list = int_to_bin_list(val=b1, max_bits=32)



# out_list = carry_free_add(
    # a_list=carry_free_add(a_list=a0_list, b_list=a1_list),
    # b_list=carry_free_add(a_list=b0_list, b_list=b1_list)
# )
# assert bits_to_int(bits=redundant_repr_to_binary(a_list=out_list)) == (a0+a1+b0+b1)

# print(int_to_bin_list(val=-23394,max_bits=64))
# tmp = multiplier(a_list=a0_list, b_list=b0_list)
# print(tmp)
# print(bits_to_int(bits=tmp))
# print((a0*b0))





# note2: References from which I borrowed CLA:
# - https://web.stanford.edu/class/archive/ee/ee371/ee371.1066/lectures/lect_04.2up.pdf
# - https://users.encs.concordia.ca/~asim/COEN_6501/Lecture_Notes/Parallel%20prefix%20adders%20presentation.pdf
# - https://gwern.net/doc/cs/algorithm/1973-kogge.pdf: Paper in which kogge & stone show parallel method to compute
#   any recurrance relation in log n depth (carry recurrance eq. (i.e. (g_out, p_out) = (g_in1 + p_in1 g_in2, p_in1 p_in2)) used in prefix adders 
#   is just one application)

# note: Framework for redudant representation system with bounded carry propogation chains - https://userpages.cs.umbc.edu/phatak/publications/hsdtrc.pdf