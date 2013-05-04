#!/usr/bin/env python
###########################################################################
# Simplified DES implementation Algorithm described in APPENDIX G of
# Cryptography and Network Security (5ed) by William Stallings
#
# Satyendra Gurjar    4/28/2013
###########################################################################

import collections
import itertools
import time

USE_MODIFIED_S0=False
QUIET=True

def timeit(method):
    def timed(*args, **kw):
        ts = time.time()
        result = method()
        te = time.time()
        print '^^^^elapsed %s secs' % (te - ts)
        return result

    return timed

def xor_bit(bit1,bit2): return ('0','1')[bit1!=bit2] # a==b -> 0, a!=b -> 1

def xor(bits1, bits2):
    assert len(bits1)==len(bits2)
    return [xor_bit(bits1[i],bits2[i]) for i in range(len(bits1))]

def bits2dec(twobits): return {'00':0,'01':1,'10':2,'11':3}[twobits]

def dec2bits(n): return {0:'00',1:'01',2:'10',3:'11'}[n]

def permutation(bits,iterable):
    return [bits[i-1] for i in iterable] # iterable index starts with 1

def left_rotate(bits, n):
    """If n is negative, rotate to the left"""
    return right_rotate(bits,-n)

def right_rotate(bits, n):
    bits = collections.deque(bits)
    bits.rotate(n) # n < 0 left o/w right
    return list(bits)

def p10(bits):
    """permutation of 10 bits"""
    return permutation(bits, (3,5,2,7,4,10,1,9,8,6))

def p8(bits):
    """permutes 8 of the 10 bits"""
    return permutation(bits, (6,3,7,4,8,5,10,9))

def ip(bits):
    """permute using IP"""
    return permutation(bits, (2,6,3,1,4,8,5,7))

def ip_inv(bits):
    """IP inverse"""
    return permutation(bits, (4,1,3,5,7,2,8,6))

def exp_perm(bits):
    """4bits to 8bits expansion using 4 1 2 3   2 3 4 1
    returns 2 rows of bits, 4bits in each row"""
    return [permutation(bits,(4,1,2,3)),permutation(bits,(2,3,4,1))]

def sbox(bits):
    global USE_MODIFIED_S0

    S0 = [[1,0,3,2],
          [3,2,1,0],
          [0,2,1,3],
          [3,1,3,2]]

    """In the modified S0, the rows 0 and 3 are the same as described for the
    original S0, but the rows 1 and 2 have been switched.
    So row 1 is 0, 2, 1,3, and row 2 is 3, 2, 1, 0."""
    modified_S0 = [[1,0,3,2],
                   [0,2,1,3],
                   [3,2,1,0],
                   [3,1,3,2]]

    if USE_MODIFIED_S0: S0 = modified_S0

    S1 = [[0,1,2,3],
          [2,0,1,3],
          [3,0,1,0],
          [2,1,0,3]]

    def _tx(bits,sbox):
        row = bits2dec(bits[0]+bits[3]) # 1st and 4th bits row in S-box
        col = bits2dec(bits[1]+bits[2]) # 2nd and 3rd bits col in S-box
        return dec2bits(sbox[row][col])

    s0bits = _tx(bits[0],S0)
    s1bits = _tx(bits[1],S1)

    return s0bits + s1bits

def p4(bits): return permutation(bits,(2,4,3,1))

def F(bits4, k):
    bits8 = exp_perm(bits4)
    bits8 = [xor(bits8[0],k[0:4]), xor(bits8[1],k[4:])]
    return p4(sbox(bits8))

def switch(bits8):
    sw = bits8[4:] + bits8[0:4]
    if not QUIET: print "  after switch", sw
    return sw

def f_k(bits,k):
    L = bits[ :4]
    R = bits[4: ]
    return ''.join(xor(L,F(R,k))) + ''.join(R)

def subkeys(key):
    p_10  = p10(key)
    left5 = left_rotate(p_10[ :5],1)
    rght5 = left_rotate(p_10[5: ],1)
    k1    = p8(left5 + rght5)
    left5 = left_rotate(left5,2)
    rght5 = left_rotate(rght5,2)
    k2    = p8(left5 + rght5)
    return k1,k2

def sdes(bits, k1, k2): return ip_inv(f_k(switch(f_k(ip(bits),k1)),k2))

def sdes_decrypt(key, ciphertext):
    (k1,k2) = subkeys(key)
    return sdes(ciphertext,k2,k1)

def sdes_encrypt(key, plaintext):
    (k1,k2) = subkeys(key)
    return sdes(plaintext,k1,k2)

@timeit
def test5a():
    K = '1010000010'; PT= '10111101'; EXPECTED_CT = '01110101'
    print '----encrypting plaintext',PT
    CT= ''.join(sdes_encrypt(K,PT)); assert CT==EXPECTED_CT
    print '  cipher text',CT
    print '----decrypting ciphertext',CT
    PT_FROM_CT = ''.join(sdes_decrypt(K, CT)); assert PT==PT_FROM_CT
    print '  plaintext back from ciphertext',PT_FROM_CT

@timeit
def test5b():
    K  = '1011000111'; PT = '01010101'
    print '----encrypting plaintext',PT
    CT= ''.join(sdes_encrypt(K,PT))
    print '  cipher text',CT
    print '----decrypting ciphertext',CT
    PT_FROM_CT = ''.join(sdes_decrypt(K, CT)); assert PT==PT_FROM_CT
    print '  plaintext back from ciphertext',PT_FROM_CT

@timeit
def test5c():
    global USE_MODIFIED_S0; USE_MODIFIED_S0 = True
    K ='0001110011'; PT='01010100'
    print '----encrypting plaintext',PT
    CT= ''.join(sdes_encrypt(K,PT))
    print '  cipher text',CT
    print '----decrypting ciphertext',CT
    PT_FROM_CT = ''.join(sdes_decrypt(K, CT)); assert PT==PT_FROM_CT
    print '  plaintext back from ciphertext',PT_FROM_CT

@timeit
def sdes_brute_force_attack():
    PT= '10111101'
    CT= '01110101'
    K = '1010000010'

    print "----PT",PT,"CT",CT,"K",K
    
    assert ''.join(sdes_decrypt(K,CT)) == PT
    assert ''.join(sdes_encrypt(K,PT)) == CT

    # now find key by trying all 10bits keys
    for K_ in itertools.product("01",repeat=10):
        K_ = ''.join(K_)
        PT_ = ''.join(sdes_decrypt(K_, CT))
        if PT == PT_:
            if K != K_:
                print "\ndecrypt: found different key then K, PT", PT_, "K", K_
            else:
                print "\ndecrypt: found same key as K, PT       ", PT_, "K", K_

        CT_ = ''.join(sdes_encrypt(K_, PT))
        if CT == CT_:
            if K != K_:
                print "decrypt: found different key then K, CT", CT_, "K", K_
            else:
                print "decrypt: found same key as K, CT       ", CT_, "K", K_

##################################################
if __name__ == '__main__':
    print "\n5a"; test5a()
    print "\n5b"; test5b()
    print "\n5c"; test5c()
    
    print "\nsdes_brute_force_attack"; sdes_brute_force_attack()