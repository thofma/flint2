/* 

Copyright 2009, 2011 William Hart. All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are
permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, this list of
      conditions and the following disclaimer.

   2. Redistributions in binary form must reproduce the above copyright notice, this list
      of conditions and the following disclaimer in the documentation and/or other materials
      provided with the distribution.

THIS SOFTWARE IS PROVIDED BY William Hart ``AS IS'' AND ANY EXPRESS OR IMPLIED
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL William Hart OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The views and conclusions contained in the software and documentation are those of the
authors and should not be interpreted as representing official policies, either expressed
or implied, of William Hart.

*/

#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>
#include "flint.h"
#include "ulong_extras.h"
#include "fft.h"

/* set p = 2^wn + 1 */
void set_p(mpz_t p, mp_size_t n, mp_bitcnt_t w)
{
   mpz_set_ui(p, 1);
   mpz_mul_2exp(p, p, n*w);
   mpz_add_ui(p, p, 1);
}

void ref_adjust(mpz_t r, mpz_t i1, mpz_t p, mp_size_t i, mp_size_t w)
{
   mpz_mul_2exp(r, i1, w*i);
   mpz_mod(r, r, p);
}

int
main(void)
{
    mp_size_t c, bits, j, k, n, w, limbs;
    mpz_t p, m2a, m2b, mn1;
    mp_limb_t * nn1, * r1;
   
    flint_rand_t state;

    flint_printf("adjust....");
    fflush(stdout);

    flint_randinit(state);
    _flint_rand_init_gmp(state);

    mpz_init(p);
    mpz_init(m2a);
    mpz_init(m2b);
    mpz_init(mn1);
   
    for (bits = FLINT_BITS; bits < 20*FLINT_BITS; bits += FLINT_BITS)
    {
        for (j = 1; j < 10; j++)
        {
            for (k = 1; k <= FLINT_BITS; k <<= 1)
            {
                n = bits/k;
                w = j*k;

                limbs = (n*w)/FLINT_BITS;

                for (c = 0; c < n; c++)
                {
                    set_p(p, n, w);
                    
                    nn1 = flint_malloc((limbs+1)*sizeof(mp_limb_t));
                    r1 = flint_malloc((limbs+1)*sizeof(mp_limb_t));

                    random_fermat(nn1, state, limbs); 
                    fermat_to_mpz(mn1, nn1, limbs);
                    ref_adjust(m2a, mn1, p, c, w);
            
                    fft_adjust(r1, nn1, c, limbs, w);
                    fermat_to_mpz(m2b, r1, limbs);
                    
                    mpz_mod(m2a, m2a, p);
                    mpz_mod(m2b, m2b, p);
                    
                    if (mpz_cmp(m2a, m2a) != 0)
                    {
                        flint_printf("FAIL:\n");
                        flint_printf("adjust error a\n");
                        flint_printf("limbs = %wd\n", limbs);
                        flint_printf("n = %wd, w = %wd, c = %wd\n", n, w, c);
                        gmp_printf("want %Zx\n\n", m2a);
                        gmp_printf("got  %Zx\n", m2b);
                        abort();
                    }
                    
                    flint_free(nn1);
                    flint_free(r1);
                }
            }
        }
    }

    mpz_clear(p);
    mpz_clear(m2a);
    mpz_clear(m2b);
    mpz_clear(mn1);

    flint_randclear(state);
    flint_cleanup();
    flint_printf("PASS\n");
    return 0;
}
