def bits_to_signed_int(bits: list[int]) -> int:
    '''
    Converts bit array to signed integer
    '''
    out = 0
    for i in range(len(bits)):
        out += (1<<i)*bits[i]

    max_interval = 1<<len(bits)
    if out > max_interval//2:
        return -(max_interval-out)
    else:
        return out

def bits_to_unsigned_int(bits: list[int]) -> int:
    out = 0
    for i in range(len(bits)):
        out += (1<<i)*bits[i]
    return out


def signed_int_to_bin_list(val, max_bits):
    v = val
    if val < 0:
        v = (1<<max_bits)+val

    digits = []
    while v > 0 or len(digits) < max_bits:
        digits.append(v % 2)
        v //= 2
    return digits

def unsigned_int_to_bin_list(val, max_bits):
    assert val>0
    v = val

    digits = []
    while v > 0 or len(digits) < max_bits:
        digits.append(v % 2)
        v //= 2
    return digits