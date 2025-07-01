from utils import bits_to_signed_int, bits_to_unsigned_int, signed_int_to_bin_list, unsigned_int_to_bin_list
import random

def carry_free_add(a_list: list[int], b_list: list[int]) -> list[int]:
    '''
    a + b using carry free adder (CFA)

    CFA eliminates long dependency chain and proceeds in two steps (depth = 2 better than logn n depth for CLA). 
    In the first step it computes immediate s_i and carry c_i+1. In the second step, c_i+1 is added to the next 
    highest sum bit s_i+1.

    CFA uses redundant representation. For more details re. CFA refer to the following papers:
    - (1) https://userpages.cs.umbc.edu/phatak/645/supl/takagi-binary-sd-rules-1985.pdf
    - (2) https://web.ece.ucsb.edu/~parhami/pubs_folder/parh88-ieeetc-add-recoded-bsd.pdf by Parhami

    Resources for CFA using redundant representation are available widely. We use positive and negative 
    redundant encoding which I suspect was first proposed by Parhami in (2).

    CFA requires 1 CLA at the end, which still has logn depth. The following resource (3) https://annas-archive.org/scidb/10.1109/4.509863/
    replaces CLA with bunch of select operations (i.e. MUXs). It does so by mandating that any i^th pair (ai, bi) == (1, 1)
    is replaced with (0,0) (CFA treats both pairs (1,1) and (0,0,) as -1). However,  it's not yet clear how this helps in our use-case.
    '''

    imm_sums = []
    imm_carries = []
    for i in range(len(a_list)):
        prev_ai = 0
        prev_bi = 0
        if i != 0:
            prev_ai = a_list[i-1]
            prev_bi = b_list[i-1]
        
        curr_ai = a_list[i]
        curr_bi = b_list[i]

        si = 0
        ci = 0 
        hit_one = False
        if curr_ai == 1 and curr_bi == 1:
            si = 0
            ci = 1
            hit_one = True
        elif (curr_ai == 1 and curr_bi == 0) or (curr_ai == 0 and curr_bi == 1):
            if prev_ai != -1 and prev_bi != -1:
                ci = 1
                si = -1
            else:
                ci = 0 
                si = 1
            hit_one = True
        elif (curr_ai == 0 and curr_bi == 0) or (curr_ai == 1 and curr_bi == -1) or (curr_ai == -1 and curr_bi == 1):
            ci = 0 
            si = 0 
            hit_one = True
        elif (curr_ai == 0 and curr_bi == -1) or (curr_ai == -1 and curr_bi == 0):
            if prev_ai != -1 and prev_bi != -1:
                ci = 0 
                si = -1
            else:
                ci = -1
                si = 1
            hit_one = True
        elif (curr_ai == -1 and curr_bi == -1):
            ci = -1
            si = 0
            hit_one = True
        assert hit_one == True

        imm_sums.append(si)
        imm_carries.append(ci)
    
    z_sum = imm_sums
    for i in range(1, len(a_list)):
        z_sum[i] = z_sum[i] + imm_carries[i-1]

    # y_minus = bits_to_int(bits=[1 if ai == -1 else 0 for ai in z_sum])
    # y_plus = bits_to_int(bits=[1 if ai == 1 else 0 for ai in z_sum])
    return z_sum

def cfa_redundant_repr_to_binary(a_list: list[int]) -> list[int]:
    '''
    Converts redudant representation used in CFA to binary representation

    We use positive and negative redudant representation. Given redudant representation
    (F^+, F^-), its binary representation Z = F^+ - (F^-) = F^+ + Complement(F^-) + 1 (2's complement)
    '''

    # z = f^+ - f^- = f^+ + f^- + 1
    not_y_minus = [0 if ai == -1 else 1 for ai in a_list]
    y_plus = [1 if ai == 1 else 0 for ai in a_list]
    (out, c) = ripple_carry_adder(a_list=y_plus, b_list=not_y_minus, cin=1)
    return out

def ripple_carry_adder(a_list: list[int], b_list:list[int], cin: int) -> tuple[list[int], int]:
    '''
    Simple ripple carry adder
    '''
    assert len(a_list) == len(b_list)

    c = cin
    out = []
    for i in range(len(a_list)):
        w = a_list[i]+b_list[i]+c
        c = w//2
        out.append(w%2)
    
    return (out, c)

def signed_multiplier(a_list: list[int], b_list: list[int]) -> list[int]:
    '''
    Any value A in 2's complement can be written as:
        -2^{n-1} A0 + A1 
    where,
        A1 = \sum_0^{n-2} 2^{i} a_i
        A0 = a31
        A = (a0, ..., a31)_2 

    Re-write inputs A, B as:
        A = -2^31 A0 + A1
        B = -2^31 B0 + B1

    then multiplication should yield:
        - (+, +) = A1B1
        - (-, -) = 2^62 - 2^31 B1 - 2^31 A1 + A1B1
        - (-, +) = A1B1 - 2^31 B1
        - (+, -) = A1B1 - 2^31 A1
    
    To multipyl we:
    (1) Calculate A1B1 (using unsigned multiplication).
    (2) Separately calculate -2^31 A1, -2^31 B1. 
    (3) Calculate T = -2^31 A1 -2^31 B1 + 2^62 (each term is added conditionally dependent on the signs of the inputs)
    (4) Output T + A1B1

    Note(1): Calculation of -2^31 A is handled with CSA. First 2^31 A is computed by padding A ([0*31]+ A + [0,0]). Then computed 
    value is negated (i.e. ~(2^31 A) + 1) by taking its complement and adding 1 to it using CSA.
    '''
    assert len(a_list) == len(b_list)
    n = len(a_list)

    partials = [[0 for _ in range(2*n)] for _ in range(n-1)]
    for i in range(n-1):
        for j in range(n-1):
            partials[i][i+j] = a_list[j] * b_list[i]

    # - 2^n-1 A1
    compl_a1 = [0 for _ in range(2*n)]
    carry_a1 = [0 for _ in range(2*n)]
    if b_list[-1] == 1:
        compl_a1 = [0 for _ in range(n-1)] + a_list[:-1] + [0, 0]
        compl_a1 = [0 if ai == 1 else 1 for ai in compl_a1]
        carry_a1[0] = 1

    # - 2^n-1 B1
    compl_b1 = [0 for _ in range(2*n)]
    carry_b1 = [0 for _ in range(2*n)]
    if a_list[-1] == 1:    
        compl_b1 = [0 for _ in range(n-1)] + b_list[:-1] + [0, 0]
        compl_b1 = [0 if ai == 1 else 1 for ai in compl_b1]
        carry_b1[0] = 1

    # 2^(2(n-1))
    extra = [0 for _ in range(2*n)]
    if a_list[-1] == 1 and b_list[-1]:
        extra[2*n-2] = 1


    neg_a1 = carry_free_add(a_list=compl_a1, b_list=carry_a1)
    neg_b1 = carry_free_add(a_list=compl_b1, b_list=carry_b1)
    extra0 = carry_free_add(a_list=neg_a1, b_list=neg_b1)
    extra0 = carry_free_add(a_list=extra0, b_list=extra)

    partials.append(extra0)

    skip = 2
    while skip <= n:
        for i in range(0, len(partials), skip):
            partials[i] = carry_free_add(a_list=partials[i], b_list=partials[i+(skip//2)])
        skip*=2

    return partials[0]


def unsigned_multiplier(a_list: list[int], b_list: list[int]) -> list[int]:
    '''
    Multiples n bit values a*b and returns 2*n bit product (in CFA redudant form)

    Function first computes the partials. It then accumualtes the partials
    using carry free adder in logarithmic depth (logaithmic over no. of partials;
    i.e. For n = 16 will have 16 partials (base 2) and depth to accumulate the partials is 4)

    '''
    assert len(a_list) == len(b_list)
    n = len(a_list)

    partials = [[0 for _ in range(2*n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            partials[i][i+j] = a_list[j] * b_list[i]

    skip = 2
    while skip <= n:
        for i in range(0, len(partials), skip):
            partials[i] = carry_free_add(a_list=partials[i], b_list=partials[i+(skip//2)])
        skip*=2

    return partials[0]


def booth_signed_multiplier(a_list: list[int], b_list: list[int]) -> list[int]:
    '''
    Booth radix-4 signed multiplication. Returns the 2*n product in CFA redudant form.

    Following is description of modified booth radix-4 booth encoding: 

    Multiplication of A x B can be expressed as summation of multiples of A (i.e. multiples of
    the multiplicand). For ex,
        A x B  = b0xA + b1xA + b2xA + b3xA 
        where (b0, b1, b2, b3)_4 is radix-4 representation of B
    bi can be in range (0, 3). Calculating 2A is a simple left shift but 3A requires an 2A+A (i.e. an addtion)

    Modified booth encoding re-writes B in radix-4 such that any bi is in the set {+/- 1, +/- 2, 0}. The re-writing
    rules are simple. They build upon booth's initial radix-2 idea: He observed that a bitstring of 1s can be replaced 
    with another bitstring consisting of single 1,-1 and the rest are 0s (for example replace 1111 with 1000-1). A booth 
    encoded bitstring, in some cases, reduces no. of partials to accumulate (when B = 1111 is encoded as 1000-1, A x B = 
    A << 4 - A compared to A + A << 1 + A << 2 + A << 3).

    For signed multiplication, the partials must be signed extended (i.e. both -A, -2A must be sign extended to 2*n bits).

    Refer to Computer arithmetic algorithms by Israel Koren for more information related to Booth's encoding
    '''

    assert len(a_list) == len(b_list)
    n = len(a_list)

    two_a = [0] + a_list + [a_list[-1] for _ in range(n-1)]
    (neg_two_a, _) = ripple_carry_adder(a_list=[0 if ai == 1 else 1 for ai in two_a], b_list=[0 for _ in range(2*n)], cin=1)
    one_a = a_list + [a_list[-1] for _ in range(n)]
    (neg_one_a, _) = ripple_carry_adder(a_list=[0 if ai == 1 else 1 for ai in one_a], b_list=[0 for _ in range(2*n)], cin=1)
    zero = [0 for _ in range(2*n)]

    # print("####")
    # print("+2A = ", two_a)
    # print("-2A = ", neg_two_a)
    # print("+A  = ", one_a)
    # print("-A  = ", neg_one_a)
    # print("####")
    
    # partials are signed extended
    partials = []

    # recode multiplier
    for i in range(n//2):
        b0 = 0
        if i != 0:
            b0 = b_list[i*2-1]
        b1 = b_list[i*2]
        b2 = b_list[i*2+1]

        coll = (b2,b1,b0)

        if (b0 == 1 and b1 == 1 and b2 == 1) or (b0 == 0 and b1 == 0 and b2 == 0):
            partials.append(zero)
            pass
        elif (b2, b1, b0) == (0,1,0) or (b2,b1,b0)==(0,0,1):
            vv = ([0]*2*i) + one_a[:(2*n-2*i)]
            partials.append(vv)
            pass
        elif coll == (1,0,0):
            vv = ([0]*2*i) + neg_two_a[:(2*n-2*i)]
            partials.append(vv)
            pass
        elif coll == (1,1,0) or coll == (1,0,1):
            vv = ([0]*2*i) + neg_one_a[:(2*n-2*i)]
            partials.append(vv)
            pass
        elif coll == (0,1,1):
            vv = ([0]*2*i) + two_a[:(2*n-2*i)]
            partials.append(vv)
            pass
    
    # print("### PARTIALS ####")
    # for i, sublist in enumerate(partials):
    #     for item in sublist:
    #         print(f"{item} ", end="")
    #     print()
    # print("#### ###### ####")

    # add the partials
    skip = 2
    while skip <= n//2:
        for i in range(0, n//2, skip):
            partials[i] = carry_free_add(a_list=partials[i], b_list=partials[i+skip//2])
        skip*=2

    return partials[0]   


def test_booth_signed_multiplier(max_bits: int):
    # input range = [-2^(max_bits-1), 2^(max_bits-1)]
    a = random.randint(a=-(1<<(max_bits-1)), b=(1<<(max_bits-1))-1)
    b = random.randint(a=-(1<<(max_bits-1)), b=(1<<(max_bits-1))-1)

    a_list = signed_int_to_bin_list(val=a, max_bits=max_bits)
    b_list = signed_int_to_bin_list(val=b, max_bits=max_bits)

    mul_out_list_redundant = booth_signed_multiplier(a_list=a_list, b_list=b_list)
    mul_out_list_bin = cfa_redundant_repr_to_binary(a_list=mul_out_list_redundant)
    mul_out = bits_to_signed_int(bits=mul_out_list_bin)
    assert mul_out == a*b, f"{a}x{b}: expected={a*b}, got {mul_out}"

def test_unsigned_muliplier(max_bits: int):
    # input range = [0, 2^(max_bits))
    a = random.randint(a=0, b=(1<<max_bits)-1)
    b = random.randint(a=0, b=(1<<max_bits)-1)

    a_list = unsigned_int_to_bin_list(val=a, max_bits=max_bits)
    b_list = unsigned_int_to_bin_list(val=b, max_bits=max_bits)

    out_list_red = unsigned_multiplier(a_list=a_list, b_list=b_list)
    out_list = cfa_redundant_repr_to_binary(a_list=out_list_red)
    out = bits_to_unsigned_int(bits=out_list)
    assert out == a*b, f"{a}x{b}: expected={a*b}, got {out}"

def test_signed_muliplier(max_bits: int):
    # input range = [-2^(max_bits-1), 2^(max_bits-1)]
    a = random.randint(a=-(1<<(max_bits-1)), b=(1<<(max_bits-1))-1)
    b = random.randint(a=-(1<<(max_bits-1)), b=(1<<(max_bits-1))-1)

    a_list = signed_int_to_bin_list(val=a, max_bits=max_bits)
    b_list = signed_int_to_bin_list(val=b, max_bits=max_bits)

    out_list_red = signed_multiplier(a_list=a_list, b_list=b_list)
    out_list = cfa_redundant_repr_to_binary(a_list=out_list_red)
    out = bits_to_signed_int(bits=out_list)
    assert out == a*b, f"{a}x{b}: expected={a*b}, got {out}"
    

for _ in range(1000):
    # test_unsigned_muliplier(max_bits=32)
    # test_booth_signed_multiplier(max_bits=32)
    test_signed_muliplier(max_bits=32)