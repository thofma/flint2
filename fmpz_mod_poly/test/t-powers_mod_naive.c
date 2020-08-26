/*
    Copyright (C) 2020 William Hart

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <https://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>
#include "flint.h"
#include "fmpz_vec.h"
#include "fmpz_mod_poly.h"
#include "ulong_extras.h"

int
main(void)
{
    int i, result;
    FLINT_TEST_INIT(state);

    flint_printf("powers_mod_naive....");
    fflush(stdout);

    /* Compare with powmod */
    for (i = 0; i < 100 * flint_test_multiplier(); i++)
    {
        fmpz_mod_poly_t f, g, pow;
        fmpz_mod_poly_struct * res;
        fmpz_t n;
        ulong exp;
        slong j;

        fmpz_init(n);

        fmpz_randprime(n, state, 100, 0);
        exp = n_randint(state, 32);

        fmpz_mod_poly_init(f, n);
        fmpz_mod_poly_init(g, n);
        fmpz_mod_poly_init(pow, n);

        res = (fmpz_mod_poly_struct *) flint_malloc(exp*sizeof(fmpz_mod_poly_struct));

        for (j = 0; j < exp; j++)
            fmpz_mod_poly_init(res + j, n);

        fmpz_mod_poly_randtest(f, state, n_randint(state, 50));
        fmpz_mod_poly_randtest_not_zero(g, state, n_randint(state, 50) + 1);
        
        fmpz_mod_poly_powers_mod_naive(res, f, exp, g);

        result = 1;
        j = 0;

        if (exp > 0)
        {
            fmpz_mod_poly_one(pow);
            result = fmpz_mod_poly_equal(res + 0, pow);
        }

        for (j = 1 ; j < exp && result; j++)
        {
            fmpz_mod_poly_mulmod(pow, pow, f, g);
            result &= fmpz_mod_poly_equal(res + j, pow);
        }

        j--;

        if (!result)
        {
            flint_printf("FAIL:\n");
            flint_printf("exp: %wu\n\n", exp);
            flint_printf("f:\n"); fmpz_mod_poly_print(f), flint_printf("\n\n");
            flint_printf("g:\n"); fmpz_mod_poly_print(g), flint_printf("\n\n");
            flint_printf("j: %w\n", j);
            flint_printf("pow:\n"); fmpz_mod_poly_print(pow), flint_printf("\n\n");
            flint_printf("res[%w]:\n", j); fmpz_mod_poly_print(res + j), flint_printf("\n\n");
            abort();
        }

        fmpz_mod_poly_clear(f);
        fmpz_mod_poly_clear(g);
        fmpz_mod_poly_clear(pow);

        for (j = 0; j < exp; j++)
            fmpz_mod_poly_clear(res + j);

        flint_free(res);

        fmpz_clear(n);
    }

    FLINT_TEST_CLEANUP(state);
    
    flint_printf("PASS\n");
    return 0;
}
